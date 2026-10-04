// Copyright (c) 2014-2024, The Monero Project
// 
// All rights reserved.
// 
// Redistribution and use in source and binary forms, with or without modification, are
// permitted provided that the following conditions are met:
// 
// 1. Redistributions of source code must retain the above copyright notice, this list of
//    conditions and the following disclaimer.
// 
// 2. Redistributions in binary form must reproduce the above copyright notice, this list
//    of conditions and the following disclaimer in the documentation and/or other
//    materials provided with the distribution.
// 
// 3. Neither the name of the copyright holder nor the names of its contributors may be
//    used to endorse or promote products derived from this software without specific
//    prior written permission.
// 
// THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND ANY
// EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
// MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL
// THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
// SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
// PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
// INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT,
// STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF
// THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
// 
// Parts of this file are originally copyright (c) 2012-2013 The Cryptonote developers

/*!
 * \file simplewallet.cpp
 * 
 * \brief Source file that defines simple_wallet class.
 */

// use boost bind placeholders for now
#define BOOST_BIND_GLOBAL_PLACEHOLDERS 1
#include <boost/bind.hpp>

#include <locale.h>
#include <iostream>
#include <sstream>
#include <fstream>
#include <string_view>
#include <boost/lexical_cast.hpp>
#include <boost/program_options.hpp>
#include <boost/algorithm/string.hpp>
#include <boost/format.hpp>
#include <boost/regex.hpp>
#include <boost/range/adaptor/transformed.hpp>
#include <boost/filesystem.hpp>
#include "include_base_utils.h"
#include "console_handler.h"
#include "common/command_line.h"
#include "common/util.h"
#include "common/scoped_message_writer.h"
#include "simplewallet.h"
#include "cryptonote_basic/cryptonote_format_utils.h"
#include "storages/http_abstract_invoke.h"
#include "rpc/core_rpc_server_commands_defs.h"
#include "mnemonics/electrum-words.h"
#include "multisig/multisig.h"
#include "wallet/wallet_args.h"
#include "wallet/fee_priority.h"
#include "version.h"
#include <stdexcept>
#include "wallet/message_store.h"
#include "QrCode.hpp"

#ifdef WIN32
#include <boost/locale.hpp>
#include <fcntl.h>
#endif

#ifdef HAVE_READLINE
#include "readline_buffer.h"
#endif

using namespace std;
using namespace epee;
using namespace cryptonote;
using boost::lexical_cast;
namespace po = boost::program_options;
typedef cryptonote::simple_wallet sw;
using tools::fee_priority;

#undef MONERO_DEFAULT_LOG_CATEGORY
#define MONERO_DEFAULT_LOG_CATEGORY "wallet.simplewallet"

#define EXTENDED_LOGS_FILE "wallet_details.log"

#define OLD_AGE_WARN_THRESHOLD (30 * 86400 / DIFFICULTY_TARGET_V2) // 30 days

#define LOCK_IDLE_SCOPE() \
  bool auto_refresh_enabled = m_auto_refresh_enabled.load(std::memory_order_relaxed); \
  m_auto_refresh_enabled.store(false, std::memory_order_relaxed); \
  /* stop any background refresh and other processes, and take over */ \
  m_wallet->stop(); \
  boost::unique_lock<boost::mutex> lock(m_idle_mutex); \
  m_idle_cond.notify_all(); \
  const epee::scope_guard scope_exit_handler([&](){ \
    /* m_idle_mutex is still locked here */ \
    m_auto_refresh_enabled.store(auto_refresh_enabled, std::memory_order_relaxed); \
    m_idle_cond.notify_one(); \
  })

#define SCOPED_WALLET_UNLOCK_ON_BAD_PASSWORD(code) \
  LOCK_IDLE_SCOPE(); \
  boost::optional<tools::password_container> pwd_container = boost::none; \
  if (m_wallet->ask_password() && !(pwd_container = get_and_verify_password())) { code; } \
  tools::wallet_keys_unlocker unlocker(*m_wallet, pwd_container ? &pwd_container->password() : nullptr);

#define SCOPED_WALLET_UNLOCK() SCOPED_WALLET_UNLOCK_ON_BAD_PASSWORD(return true;)

#define PRINT_USAGE(usage_help) fail_msg_writer() << boost::format(tr("用法：%s")) % usage_help;

#define LONG_PAYMENT_ID_SUPPORT_CHECK() \
  do { \
    fail_msg_writer() << tr("错误：长支付 ID 已废弃。"); \
    fail_msg_writer() << tr("长支付 ID 不会在区块链上加密，会损害您的隐私。"); \
    fail_msg_writer() << tr("如果收款方仍要求使用长支付 ID，请通知对方。"); \
    return true; \
  } while(0)

#define REFRESH_PERIOD 90 // seconds

#define MAX_MNEW_ADDRESSES 65536

#define CHECK_MULTISIG_ENABLED() \
  do \
  { \
    if (!m_wallet->is_multisig_enabled()) \
    { \
      fail_msg_writer() << tr("多重签名功能已禁用。"); \
      fail_msg_writer() << tr("多重签名功能仍处于实验阶段，可能存在错误。可能出现的问题包括：发送到多重签名钱包的资金完全无法使用，只能在恶意成员参与的情况下使用，或被恶意成员窃取。"); \
      fail_msg_writer() << tr("您可以使用以下命令启用："); \
      fail_msg_writer() << tr("  set enable-multisig-experimental 1"); \
      return false; \
    } \
  } while(0)

#define CHECK_IF_BACKGROUND_SYNCING(msg) \
  do \
  { \
    if (m_wallet->is_background_wallet() || m_wallet->is_background_syncing()) \
    { \
      std::string type = m_wallet->is_background_wallet() ? "background wallet" : "background syncing wallet"; \
      fail_msg_writer() << boost::format(tr("%s %s")) % type % msg; \
      return false; \
    } \
  } while (0)

namespace
{
  constexpr std::array<std::string_view, 5> allowed_priority_strings = tools::fee_priority_utilities::fee_priority_strings;
  const auto arg_wallet_file = wallet_args::arg_wallet_file();
  const command_line::arg_descriptor<std::string> arg_wallet_dir = {"wallet-dir", sw::tr("查找和保存钱包文件的目录。路径必须是绝对路径；如果同时指定了绝对路径的钱包文件，则忽略此目录。"), ""};
  const command_line::arg_descriptor<std::string> arg_generate_new_wallet = {"generate-new-wallet", sw::tr("生成新钱包并保存到 <arg>"), ""};
  const command_line::arg_descriptor<std::string> arg_generate_from_device = {"generate-from-device", sw::tr("从设备生成新钱包并保存到 <arg>"), ""};
  const command_line::arg_descriptor<std::string> arg_generate_from_view_key = {"generate-from-view-key", sw::tr("使用查看密钥生成仅接收钱包"), ""};
  const command_line::arg_descriptor<std::string> arg_generate_from_spend_key = {"generate-from-spend-key", sw::tr("使用支出密钥生成确定性钱包"), ""};
  const command_line::arg_descriptor<std::string> arg_generate_from_keys = {"generate-from-keys", sw::tr("使用私钥生成钱包"), ""};
  const command_line::arg_descriptor<std::string> arg_generate_from_multisig_keys = {"generate-from-multisig-keys", sw::tr("使用多重签名钱包密钥生成主钱包"), ""};
  const auto arg_generate_from_json = wallet_args::arg_generate_from_json();
  const command_line::arg_descriptor<std::string> arg_mnemonic_language = {"mnemonic-language", sw::tr("助记词语言"), ""};
  const command_line::arg_descriptor<std::string> arg_electrum_seed = {"electrum-seed", sw::tr("指定用于恢复/创建钱包的 Electrum 助记词"), ""};
  const command_line::arg_descriptor<bool> arg_restore_deterministic_wallet = {"restore-deterministic-wallet", sw::tr("使用 Electrum 风格助记词恢复钱包"), false};
  const command_line::arg_descriptor<bool> arg_restore_from_seed = {"restore-from-seed", sw::tr("--restore-deterministic-wallet 的别名"), false};
  const command_line::arg_descriptor<bool> arg_restore_multisig_wallet = {"restore-multisig-wallet", sw::tr("使用 Electrum 风格助记词恢复多重签名钱包"), false};
  const command_line::arg_descriptor<bool> arg_non_deterministic = {"non-deterministic", sw::tr("生成非确定性的查看密钥和支出密钥"), false};
  const command_line::arg_descriptor<uint64_t> arg_restore_height = {"restore-height", sw::tr("从指定区块高度恢复"), 0};
  const command_line::arg_descriptor<std::string> arg_restore_date = {"restore-date", sw::tr("从指定日期估算的区块高度恢复"), ""};
  const command_line::arg_descriptor<bool> arg_do_not_relay = {"do-not-relay", sw::tr("新创建的交易不会广播到 Monero 网络"), false};
  const command_line::arg_descriptor<bool> arg_create_address_file = {"create-address-file", sw::tr("为新钱包创建地址文件"), false};
  const command_line::arg_descriptor<std::string> arg_subaddress_lookahead = {"subaddress-lookahead", tools::wallet2::tr("设置子地址预生成范围为 <major>:<minor>"), ""};
  const command_line::arg_descriptor<bool> arg_use_english_language_names = {"use-english-language-names", sw::tr("显示英文语言名称"), false};
  const command_line::arg_descriptor<bool> arg_use_legacy_seed = {"use-legacy-seed", sw::tr("使用 25 词传统助记词，而不是 Polyseed"), false};

  const command_line::arg_descriptor< std::vector<std::string> > arg_command = {"command", ""};

  const char* USAGE_START_MINING("start_mining [<number_of_threads>] [bg_mining] [ignore_battery]");
  const char* USAGE_SET_DAEMON("set_daemon <host>[:<port>] [trusted|untrusted|this-is-probably-a-spy-node]");
  const char* USAGE_SHOW_BALANCE("balance [detail]");
  const char* USAGE_INCOMING_TRANSFERS("incoming_transfers [available|unavailable] [verbose] [uses] [index=<N1>[,<N2>[,...]]]");
  const char* USAGE_PAYMENTS("payments <PID_1> [<PID_2> ... <PID_N>]");
  const char* USAGE_PAYMENT_ID("payment_id");
  const char* USAGE_TRANSFER("transfer [index=<N1>[,<N2>,...]] [<priority>] [<ring_size>] (<URI> | <address> <amount>) [subtractfeefrom=<D0>[,<D1>,all,...]] [<payment_id>]");
  const char* USAGE_SWEEP_ALL("sweep_all [index=<N1>[,<N2>,...] | index=all] [<priority>] [<ring_size>] [outputs=<N>] <address> [<payment_id (obsolete)>]");
  const char* USAGE_SWEEP_ACCOUNT("sweep_account <account> [index=<N1>[,<N2>,...] | index=all] [<priority>] [<ring_size>] [outputs=<N>] <address> [<payment_id (obsolete)>]");
  const char* USAGE_SWEEP_BELOW("sweep_below <amount_threshold> [index=<N1>[,<N2>,...]] [<priority>] [<ring_size>] <address> [<payment_id (obsolete)>]");
  const char* USAGE_SWEEP_SINGLE("sweep_single [<priority>] [<ring_size>] [outputs=<N>] <key_image> <address> [<payment_id (obsolete)>]");
  const char* USAGE_DONATE("donate [index=<N1>[,<N2>,...]] [<priority>] [<ring_size>] <amount>");
  const char* USAGE_SIGN_TRANSFER("sign_transfer [export_raw] [<filename>]");
  const char* USAGE_SET_LOG("set_log <level>|{+,-,}<categories>");
  const char* USAGE_ACCOUNT("account\n"
                            "  account new <label text with white spaces allowed>\n"
                            "  account switch <index> \n"
                            "  account label <index> <label text with white spaces allowed>\n"
                            "  account tag <tag_name> <account_index_1> [<account_index_2> ...]\n"
                            "  account untag <account_index_1> [<account_index_2> ...]\n"
                            "  account tag_description <tag_name> <description>");
  const char* USAGE_ADDRESS("address [ new <label text with white spaces allowed> | mnew <amount of new addresses> | all | <index_min> [<index_max>] | label <index> <label text with white spaces allowed> | device [<index>] | one-off <account> <subaddress>]");
  const char* USAGE_INTEGRATED_ADDRESS("integrated_address [device] [<payment_id> | <address>]");
  const char* USAGE_ADDRESS_BOOK("address_book [(add (<address>|<integrated address>) [<description possibly with whitespaces>])|(delete <index>)]");
  const char* USAGE_SET_VARIABLE("set <option> [<value>]");
  const char* USAGE_GET_TX_KEY("get_tx_key <txid>");
  const char* USAGE_SET_TX_KEY("set_tx_key <txid> <tx_key> [<subaddress>]");
  const char* USAGE_CHECK_TX_KEY("check_tx_key <txid> <txkey> <address>");
  const char* USAGE_GET_TX_PROOF("get_tx_proof <txid> <address> [<message>]");
  const char* USAGE_CHECK_TX_PROOF("check_tx_proof <txid> <address> <signature_file> [<message>]");
  const char* USAGE_GET_SPEND_PROOF("get_spend_proof <txid> [<message>]");
  const char* USAGE_CHECK_SPEND_PROOF("check_spend_proof <txid> <signature_file> [<message>]");
  const char* USAGE_GET_RESERVE_PROOF("get_reserve_proof (all|<amount>) [<message>]");
  const char* USAGE_CHECK_RESERVE_PROOF("check_reserve_proof <address> <signature_file> [<message>]");
  const char* USAGE_SHOW_TRANSFERS("show_transfers [in|out|all|pending|failed|pool|coinbase] [index=<N1>[,<N2>,...]] [<min_height> [<max_height>]]");
  const char* USAGE_UNSPENT_OUTPUTS("unspent_outputs [index=<N1>[,<N2>,...]] [<min_amount> [<max_amount>]]");
  const char* USAGE_RESCAN_BC("rescan_bc [hard|soft|keep_ki] [start_height=0]");
  const char* USAGE_SET_TX_NOTE("set_tx_note <txid> [free text note]");
  const char* USAGE_GET_TX_NOTE("get_tx_note <txid>");
  const char* USAGE_GET_DESCRIPTION("get_description");
  const char* USAGE_SET_DESCRIPTION("set_description [free text note]");
  const char* USAGE_SIGN("sign [<account_index>,<address_index>] [--spend|--view] <filename>");
  const char* USAGE_VERIFY("verify <filename> <address> <signature>");
  const char* USAGE_EXPORT_KEY_IMAGES("export_key_images [all] <filename>");
  const char* USAGE_IMPORT_KEY_IMAGES("import_key_images <filename>");
  const char* USAGE_HW_KEY_IMAGES_SYNC("hw_key_images_sync");
  const char* USAGE_HW_RECONNECT("hw_reconnect");
  const char* USAGE_EXPORT_OUTPUTS("export_outputs [all] <filename>");
  const char* USAGE_IMPORT_OUTPUTS("import_outputs <filename>");
  const char* USAGE_SHOW_TRANSFER("show_transfer <txid>");
  const char* USAGE_MAKE_MULTISIG("make_multisig <threshold> <string1> [<string>...]");
  const char* USAGE_EXCHANGE_MULTISIG_KEYS("exchange_multisig_keys [force-update-use-with-caution] <string> [<string>...]");
  const char* USAGE_EXPORT_MULTISIG_INFO("export_multisig_info <filename>");
  const char* USAGE_IMPORT_MULTISIG_INFO("import_multisig_info <filename> [<filename>...]");
  const char* USAGE_SIGN_MULTISIG("sign_multisig <filename>");
  const char* USAGE_SUBMIT_MULTISIG("submit_multisig <filename>");
  const char* USAGE_EXPORT_RAW_MULTISIG_TX("export_raw_multisig_tx <filename>");
  const char* USAGE_MMS("mms [<subcommand> [<subcommand_parameters>]]");
  const char* USAGE_MMS_INIT("mms init <required_signers>/<authorized_signers> <own_label> <own_transport_address>");
  const char* USAGE_MMS_INFO("mms info");
  const char* USAGE_MMS_SIGNER("mms signer [<number> <label> [<transport_address> [<monero_address>]]]");
  const char* USAGE_MMS_LIST("mms list");
  const char* USAGE_MMS_NEXT("mms next [sync]");
  const char* USAGE_MMS_SYNC("mms sync");
  const char* USAGE_MMS_TRANSFER("mms transfer <transfer_command_arguments>");
  const char* USAGE_MMS_DELETE("mms delete (<message_id> | all)");
  const char* USAGE_MMS_SEND("mms send [<message_id>]");
  const char* USAGE_MMS_RECEIVE("mms receive");
  const char* USAGE_MMS_EXPORT("mms export <message_id>");
  const char* USAGE_MMS_NOTE("mms note [<label> <text>]");
  const char* USAGE_MMS_SHOW("mms show <message_id>");
  const char* USAGE_MMS_SET("mms set <option_name> [<option_value>]");
  const char* USAGE_MMS_SEND_SIGNER_CONFIG("mms send_signer_config");
  const char* USAGE_MMS_START_AUTO_CONFIG("mms start_auto_config [<label> <label> ...]");
  const char* USAGE_MMS_CONFIG_CHECKSUM("mms config_checksum");
  const char* USAGE_MMS_STOP_AUTO_CONFIG("mms stop_auto_config");
  const char* USAGE_MMS_AUTO_CONFIG("mms auto_config <auto_config_token>");
  const char* USAGE_PRINT_RING("print_ring <key_image> | <txid>");
  const char* USAGE_SET_RING("set_ring <filename> | ( <key_image> absolute|relative <index> [<index>...] )");
  const char* USAGE_UNSET_RING("unset_ring <txid> | ( <key_image> [<key_image>...] )");
  const char* USAGE_SAVE_KNOWN_RINGS("save_known_rings");
  const char* USAGE_FREEZE("freeze <key_image>");
  const char* USAGE_THAW("thaw <key_image>");
  const char* USAGE_FROZEN("frozen <key_image>");
  const char* USAGE_LOCK("lock");
  const char* USAGE_NET_STATS("net_stats");
  const char* USAGE_PUBLIC_NODES("public_nodes");
  const char* USAGE_WELCOME("welcome");
  const char* USAGE_SHOW_QR_CODE("show_qr_code [<subaddress_index>]");
  const char* USAGE_VERSION("version");
  const char* USAGE_CLEAR("clear");
  const char* USAGE_HELP("help [<command> | all]");
  const char* USAGE_APROPOS("apropos <keyword> [<keyword> ...]");
  const char* USAGE_SCAN_TX("scan_tx <txid> [<txid> ...]");

  std::string input_line(const std::string& prompt, bool yesno = false)
  {
    PAUSE_READLINE();
    std::cout << prompt;
    if (yesno)
      std::cout << " [y/N]";
    std::cout << ": " << std::flush;

    std::string buf;
#ifdef _WIN32
    buf = tools::input_line_win();
#else
    std::getline(std::cin, buf);
#endif

    return epee::string_tools::trim(buf);
  }

  epee::wipeable_string input_secure_line(const char *prompt)
  {
    PAUSE_READLINE();
    auto pwd_container = tools::password_container::prompt(false, prompt, false);
    if (!pwd_container)
    {
      MERROR("Failed to read secure line");
      return "";
    }

    epee::wipeable_string buf = pwd_container->password();

    buf.trim();
    return buf;
  }

  boost::optional<tools::password_container> password_prompter(const char *prompt, bool verify)
  {
    PAUSE_READLINE();
    auto pwd_container = tools::password_container::prompt(verify, prompt);
    if (!pwd_container)
    {
      tools::fail_msg_writer() << sw::tr("读取密码失败");
    }
    return pwd_container;
  }

  boost::optional<tools::password_container> default_password_prompter(bool verify)
  {
    return password_prompter(verify ? sw::tr("请输入新的钱包密码") : sw::tr("钱包密码"), verify);
  }

  boost::optional<tools::password_container> background_sync_cache_password_prompter(bool verify)
  {
    return password_prompter(verify ? sw::tr("请输入后台同步缓存的自定义密码") : sw::tr("后台同步缓存密码"), verify);
  }

  inline std::string interpret_rpc_response(bool ok, const std::string& status)
  {
    std::string err;
    if (ok)
    {
      if (status == CORE_RPC_STATUS_BUSY)
      {
        err = sw::tr("守护进程正忙，请稍后再试。");
      }
      else if (status != CORE_RPC_STATUS_OK)
      {
        err = status;
      }
    }
    else
    {
      err = sw::tr("可能已与守护进程断开连接");
    }
    return err;
  }

  tools::scoped_message_writer success_msg_writer(bool color = false)
  {
    return tools::scoped_message_writer(color ? console_color_green : console_color_default, false, std::string(), el::Level::Info);
  }

  tools::scoped_message_writer message_writer(epee::console_colors color = epee::console_color_default, bool bright = false)
  {
    return tools::scoped_message_writer(color, bright);
  }

  tools::scoped_message_writer fail_msg_writer()
  {
    return tools::scoped_message_writer(console_color_red, true, sw::tr("错误："), el::Level::Error);
  }

  bool parse_bool(const std::string& s, bool& result)
  {
    if (s == "1" || command_line::is_yes(s))
    {
      result = true;
      return true;
    }
    if (s == "0" || command_line::is_no(s))
    {
      result = false;
      return true;
    }

    boost::algorithm::is_iequal ignore_case{};
    if (boost::algorithm::equals("true", s, ignore_case) || boost::algorithm::equals(simple_wallet::tr("true"), s, ignore_case))
    {
      result = true;
      return true;
    }
    if (boost::algorithm::equals("false", s, ignore_case) || boost::algorithm::equals(simple_wallet::tr("false"), s, ignore_case))
    {
      result = false;
      return true;
    }

    return false;
  }

  template <typename F>
  bool parse_bool_and_use(const std::string& s, F func)
  {
    bool r;
    if (parse_bool(s, r))
    {
      func(r);
      return true;
    }
    else
    {
      fail_msg_writer() << sw::tr("参数无效：必须为 0/1、true/false、y/n 或 yes/no");
      return false;
    }
  }

  const struct
  {
    const char *name;
    tools::wallet2::RefreshType refresh_type;
  } refresh_type_names[] =
  {
    { "full", tools::wallet2::RefreshFull },
    { "optimize-coinbase", tools::wallet2::RefreshOptimizeCoinbase },
    { "optimized-coinbase", tools::wallet2::RefreshOptimizeCoinbase },
    { "no-coinbase", tools::wallet2::RefreshNoCoinbase },
    { "default", tools::wallet2::RefreshDefault },
  };

  bool parse_refresh_type(const std::string &s, tools::wallet2::RefreshType &refresh_type)
  {
    for (size_t n = 0; n < sizeof(refresh_type_names) / sizeof(refresh_type_names[0]); ++n)
    {
      if (s == refresh_type_names[n].name)
      {
        refresh_type = refresh_type_names[n].refresh_type;
        return true;
      }
    }
    fail_msg_writer() << cryptonote::simple_wallet::tr("解析刷新类型失败");
    return false;
  }

  std::string get_refresh_type_name(tools::wallet2::RefreshType type)
  {
    for (size_t n = 0; n < sizeof(refresh_type_names) / sizeof(refresh_type_names[0]); ++n)
    {
      if (type == refresh_type_names[n].refresh_type)
        return refresh_type_names[n].name;
    }
    return "invalid";
  }

  const struct
  {
    const char *name;
    tools::wallet2::BackgroundSyncType background_sync_type;
  } background_sync_type_names[] =
  {
    { "off", tools::wallet2::BackgroundSyncOff },
    { "reuse-wallet-password", tools::wallet2::BackgroundSyncReusePassword },
    { "custom-background-password", tools::wallet2::BackgroundSyncCustomPassword },
  };

  bool parse_background_sync_type(const std::string &s, tools::wallet2::BackgroundSyncType &background_sync_type)
  {
    for (size_t n = 0; n < sizeof(background_sync_type_names) / sizeof(background_sync_type_names[0]); ++n)
    {
      if (s == background_sync_type_names[n].name)
      {
        background_sync_type = background_sync_type_names[n].background_sync_type;
        return true;
      }
    }
    fail_msg_writer() << cryptonote::simple_wallet::tr("解析后台同步类型失败");
    return false;
  }

  std::string get_background_sync_type_name(tools::wallet2::BackgroundSyncType type)
  {
    for (size_t n = 0; n < sizeof(background_sync_type_names) / sizeof(background_sync_type_names[0]); ++n)
    {
      if (type == background_sync_type_names[n].background_sync_type)
        return background_sync_type_names[n].name;
    }
    return "invalid";
  }

  std::string get_version_string(uint32_t version)
  {
    return boost::lexical_cast<std::string>(version >> 16) + "." + boost::lexical_cast<std::string>(version & 0xffff);
  }

  std::string oa_prompter(const std::string &url, const std::vector<std::string> &addresses, bool dnssec_valid)
  {
    if (addresses.empty())
      return {};
    // prompt user for confirmation.
    // inform user of DNSSEC validation status as well.
    std::string dnssec_str;
    if (dnssec_valid)
    {
      dnssec_str = sw::tr("DNSSEC 验证通过");
    }
    else
    {
      dnssec_str = sw::tr("警告：DNSSEC 验证未通过，此地址可能不正确！");
    }
    std::stringstream prompt;
    prompt << sw::tr("URL：") << url
           << ", " << dnssec_str << std::endl
           << sw::tr(" Monero 地址 = ") << addresses[0]
           << std::endl
           << sw::tr("确认无误吗？")
    ;
    // prompt the user for confirmation given the dns query and dnssec status
    std::string confirm_dns_ok = input_line(prompt.str(), true);
    if (std::cin.eof())
    {
      return {};
    }
    if (!command_line::is_yes(confirm_dns_ok))
    {
      std::cout << sw::tr("您已取消转账请求") << std::endl;
      return {};
    }
    return addresses[0];
  }

  bool parse_subaddress_indices(const std::string& arg, std::set<uint32_t>& subaddr_indices)
  {
    subaddr_indices.clear();

    if (arg.substr(0, 6) != "index=")
      return false;
    std::string subaddr_indices_str_unsplit = arg.substr(6, arg.size() - 6);
    std::vector<std::string> subaddr_indices_str;
    boost::split(subaddr_indices_str, subaddr_indices_str_unsplit, boost::is_any_of(","));

    for (const auto& subaddr_index_str : subaddr_indices_str)
    {
      uint32_t subaddr_index;
      if(!epee::string_tools::get_xtype_from_string(subaddr_index, subaddr_index_str))
      {
        fail_msg_writer() << sw::tr("解析索引失败：") << subaddr_index_str;
        subaddr_indices.clear();
        return false;
      }
      subaddr_indices.insert(subaddr_index);
    }
    return true;
  }

  boost::optional<std::pair<uint32_t, uint32_t>> parse_subaddress_lookahead(const std::string& str)
  {
    auto r = tools::parse_subaddress_lookahead(str);
    if (!r)
      fail_msg_writer() << sw::tr("子地址预生成范围格式无效；必须为 <major>:<minor>");
    return r;
  }

  static constexpr std::string_view SFFD_ARG_NAME{"subtractfeefrom="};

  bool parse_subtract_fee_from_outputs
  (
    const std::string& arg,
    tools::wallet2::unique_index_container& subtract_fee_from_outputs,
    bool& subtract_fee_from_all,
    bool& matches
  )
  {
    matches = false;
    if (!boost::string_ref{arg}.starts_with(SFFD_ARG_NAME.data())) // if arg doesn't match
      return true;
    matches = true;

    const char* arg_end = arg.c_str() + arg.size();
    for (const char* p = arg.c_str() + SFFD_ARG_NAME.size(); p < arg_end;)
    {
      const char* new_p = nullptr;
      const unsigned long dest_index = strtoul(p, const_cast<char**>(&new_p), 10);
      if (dest_index == 0 && new_p == p) // numerical conversion failed
      {
        if (0 != strncmp(p, "all", 3))
        {
          fail_msg_writer() << tr("解析手续费扣除列表失败");
          return false;
        }
        subtract_fee_from_all = true;
        break;
      }
      else if (dest_index > std::numeric_limits<uint32_t>::max())
      {
        fail_msg_writer() << tr("目标索引过大") << ": " << dest_index;
        return false;
      }
      else
      {
        subtract_fee_from_outputs.insert(dest_index);
        p = new_p + 1; // skip the comma
      }
    }

    return true;
  }
  static std::string resolve_wallet_path(const std::string &filename, const std::string &wallet_dir)
  {
    boost::filesystem::path path(filename);
    if (path.is_absolute() || wallet_dir.empty()) return filename;
    if (!boost::filesystem::path(wallet_dir).is_absolute())
    {
      fail_msg_writer() << "--wallet-dir " << tr("参数不是绝对路径，已忽略。");
      return filename;
    }
    return (boost::filesystem::path(wallet_dir) / path).string();
  }
} // anonymous namespace

void simple_wallet::handle_transfer_exception(const std::exception_ptr &e, bool trusted_daemon)
{
    bool warn_of_possible_attack = !trusted_daemon;
    try
    {
      std::rethrow_exception(e);
    }
    catch (const tools::error::deprecated_rpc_access&)
    {
      fail_msg_writer() << tr("守护进程要求使用已废弃的 RPC 支付方式。参见 https://github.com/monero-project/monero/issues/8722");
    }
    catch (const tools::error::no_connection_to_daemon&)
    {
      fail_msg_writer() << sw::tr("无法连接到守护进程，请确认守护进程正在运行。");
    }
    catch (const tools::error::daemon_busy&)
    {
      fail_msg_writer() << tr("守护进程正忙，请稍后再试。");
    }
    catch (const tools::error::wallet_rpc_error& e)
    {
      LOG_ERROR("RPC 错误：" << e.to_string());
      fail_msg_writer() << sw::tr("RPC 错误：") << e.what();
    }
    catch (const tools::error::get_outs_error &e)
    {
      fail_msg_writer() << sw::tr("获取用于混合的随机输出失败：") << e.what();
    }
    catch (const tools::error::not_enough_unlocked_money& e)
    {
      LOG_PRINT_L0(boost::format("not enough money to transfer, available only %s, sent amount %s") %
        print_money(e.available()) %
        print_money(e.tx_amount()));
      fail_msg_writer() << sw::tr("可用余额不足");
      warn_of_possible_attack = false;
    }
    catch (const tools::error::not_enough_money& e)
    {
      LOG_PRINT_L0(boost::format("not enough money to transfer, available only %s, sent amount %s") %
        print_money(e.available()) %
        print_money(e.tx_amount()));
      fail_msg_writer() << sw::tr("可用余额不足");
      warn_of_possible_attack = false;
    }
    catch (const tools::error::tx_not_possible& e)
    {
      LOG_PRINT_L0(boost::format("not enough money to transfer, available only %s, transaction amount %s = %s + %s (fee)") %
        print_money(e.available()) %
        print_money(e.tx_amount() + e.fee())  %
        print_money(e.tx_amount()) %
        print_money(e.fee()));
      fail_msg_writer() << sw::tr("无法找到创建交易的方法。通常是因为零尘金额太小，手续费无法覆盖其自身，或者发送金额超过可用余额，或者未为手续费预留足够金额");
      warn_of_possible_attack = false;
    }
    catch (const tools::error::not_enough_outs_to_mix& e)
    {
      auto writer = fail_msg_writer();
      writer << sw::tr("指定环大小没有足够的输出") << " = " << (e.mixin_count() + 1) << ":";
      for (std::pair<uint64_t, uint64_t> outs_for_amount : e.scanty_outs())
      {
        writer << "\n" << sw::tr("输出金额") << " = " << print_money(outs_for_amount.first) << ", " << sw::tr("找到的可用输出") << " = " << outs_for_amount.second;
      }
      writer << sw::tr("请使用 sweep_unmixable。");
    }
    catch (const tools::error::tx_not_constructed&)
    {
      fail_msg_writer() << sw::tr("未能构建交易");
      warn_of_possible_attack = false;
    }
    catch (const tools::error::tx_rejected& e)
    {
      fail_msg_writer() << (boost::format(sw::tr("交易 %s 被守护进程拒绝")) % get_transaction_hash(e.tx()));
      std::string reason = e.reason();
      if (!reason.empty())
        fail_msg_writer() << sw::tr("原因：") << reason;
    }
    catch (const tools::error::tx_sum_overflow& e)
    {
      fail_msg_writer() << e.what();
      warn_of_possible_attack = false;
    }
    catch (const tools::error::zero_amount&)
    {
      fail_msg_writer() << sw::tr("目标金额为零");
      warn_of_possible_attack = false;
    }
    catch (const tools::error::zero_destination&)
    {
      fail_msg_writer() << sw::tr("交易没有目标地址");
      warn_of_possible_attack = false;
    }
    catch (const tools::error::tx_too_big& e)
    {
      fail_msg_writer() << sw::tr("未能找到合适的交易拆分方式");
      warn_of_possible_attack = false;
    }
    catch (const tools::error::transfer_error& e)
    {
      LOG_ERROR("未知转账错误：" << e.to_string());
      fail_msg_writer() << sw::tr("未知转账错误：") << e.what();
    }
    catch (const tools::error::multisig_export_needed& e)
    {
      LOG_ERROR("多重签名 error: " << e.to_string());
      fail_msg_writer() << sw::tr("多重签名错误：") << e.what();
      warn_of_possible_attack = false;
    }
    catch (const tools::error::wallet_internal_error& e)
    {
      LOG_ERROR("内部错误：" << e.to_string());
      fail_msg_writer() << sw::tr("内部错误：") << e.what();
    }
    catch (const std::exception& e)
    {
      LOG_ERROR("意外错误：" << e.what());
      fail_msg_writer() << sw::tr("意外错误：") << e.what();
    }

    if (warn_of_possible_attack)
      fail_msg_writer() << sw::tr("发生错误。节点可能试图诱导您重复创建交易，从而确定哪些输出属于您；也可能确实发生了错误。建议断开与此节点的连接，并暂时不要立即发送交易。也可以连接其他节点，以避免原节点关联您的信息。");
}

namespace
{
  bool check_file_overwrite(const std::string &filename)
  {
    boost::system::error_code errcode;
    if (boost::filesystem::exists(filename, errcode))
    {
      if (boost::ends_with(filename, ".keys"))
      {
        fail_msg_writer() << boost::format(sw::tr("文件 %s 可能存储钱包私钥！请使用其他文件名。")) % filename;
        return false;
      }
      return command_line::is_yes(input_line((boost::format(sw::tr("文件 %s 已存在。确定要覆盖吗？")) % filename).str(), true));
    }
    return true;
  }

  void print_secret_key(const crypto::secret_key &k)
  {
    static constexpr const char hex[] = u8"0123456789abcdef";
    const uint8_t *ptr = (const uint8_t*)k.data;
    for (size_t i = 0, sz = sizeof(k); i < sz; ++i)
    {
      putchar(hex[*ptr >> 4]);
      putchar(hex[*ptr & 15]);
      ++ptr;
    }
  }
}

bool parse_priority(const std::string& arg, fee_priority& priority)
{
  const auto priority_optional = tools::fee_priority_utilities::from_string(arg);
  if (!priority_optional.has_value())
    return false;
  priority = priority_optional.value();
  return true;
}

std::string join_priority_strings(const char *delimiter)
{
  std::string s;
  for (size_t n = 0; n < allowed_priority_strings.size(); ++n)
  {
    if (!s.empty())
      s += delimiter;
    s += allowed_priority_strings[n];
  }
  return s;
}

std::string simple_wallet::get_commands_str()
{
  std::stringstream ss;
  ss << tr("命令：") << ENDL;
  std::string usage = m_cmd_binder.get_usage();
  boost::replace_all(usage, "\n", "\n  ");
  usage.insert(0, "  ");
  ss << usage << ENDL;
  return ss.str();
}

std::string simple_wallet::get_command_usage(const std::vector<std::string> &args)
{
  std::pair<std::string, std::string> documentation = m_cmd_binder.get_documentation(args);
  std::stringstream ss;
  if(documentation.first.empty())
  {
    ss << tr("未知命令：") << args.front();
  }
  else
  {
    std::string usage = documentation.second.empty() ? args.front() : documentation.first;
    std::string description = documentation.second.empty() ? documentation.first : documentation.second;
    usage.insert(0, "  ");
    ss << tr("命令用法：") << ENDL << usage << ENDL << ENDL;
    boost::replace_all(description, "\n", "\n  ");
    description.insert(0, "  ");
    ss << tr("命令说明：") << ENDL << description << ENDL;
  }
  return ss.str();
}

bool simple_wallet::viewkey(const std::vector<std::string> &args/* = std::vector<std::string>()*/)
{
  // don't log
  PAUSE_READLINE();
  SCOPED_WALLET_UNLOCK();
  crypto::secret_key viewkey = m_wallet->get_account().get_keys().m_view_secret_key;
  bool available = viewkey != crypto::null_skey;
  if (!available && m_wallet->key_on_device()) available = m_wallet->get_account().get_device().get_cached_view_key(viewkey);
  if (available) {
    printf("secret: ");
    print_secret_key(viewkey);
    putchar('\n');
  } else {
    std::cout << "secret: On device. Not available" << std::endl;
  }
  std::cout << "public: " << string_tools::pod_to_hex(m_wallet->get_account().get_keys().m_account_address.m_view_public_key) << std::endl;

  return true;
}

bool simple_wallet::spendkey(const std::vector<std::string> &args/* = std::vector<std::string>()*/)
{
  if (m_wallet->watch_only())
  {
    fail_msg_writer() << tr("钱包为仅观察钱包，没有支出密钥");
    return true;
  }
  CHECK_IF_BACKGROUND_SYNCING("has no spend key");
  // don't log
  PAUSE_READLINE();
  if (m_wallet->key_on_device()) {
    std::cout << "secret: On device. Not available" << std::endl;
  } else {
    SCOPED_WALLET_UNLOCK();
    printf("secret: ");
    print_secret_key(m_wallet->get_account().get_keys().m_spend_secret_key);
    putchar('\n');
  }
  std::cout << "public: " << string_tools::pod_to_hex(m_wallet->get_account().get_keys().m_account_address.m_spend_public_key) << std::endl;

  return true;
}

bool simple_wallet::print_seed(bool encrypted, bool as_legacy_seed)
{
  bool success =  false;
  epee::wipeable_string seed;

  if (m_wallet->key_on_device())
  {
    fail_msg_writer() << tr("硬件钱包不支持此命令");
    return true;
  }
  if (m_wallet->watch_only())
  {
    fail_msg_writer() << tr("钱包为仅观察钱包，没有助记词");
    return true;
  }
  CHECK_IF_BACKGROUND_SYNCING("has no seed");

  const multisig::multisig_account_status ms_status{m_wallet->get_multisig_status()};
  if (ms_status.multisig_is_active)
  {
    if (!ms_status.is_ready)
    {
      fail_msg_writer() << tr("钱包为多重签名钱包，但尚未完成设置");
      return true;
    }
    if (as_legacy_seed)
    {
      fail_msg_writer() << tr("钱包为多重签名钱包，因此没有传统助记词");
      return true;
    }
  }
  if (as_legacy_seed && !m_wallet->is_polyseed())
  {
    fail_msg_writer() << tr("只有带 Polyseed 的钱包才能显示传统助记词");
    return true;
  }
  if (encrypted && m_wallet->is_polyseed())
  {
    fail_msg_writer() << tr("钱包使用 Polyseed，无法通过此命令进行加密");
    return true;
  }

  SCOPED_WALLET_UNLOCK();

  if (!ms_status.multisig_is_active && !m_wallet->is_deterministic())
  {
    fail_msg_writer() << tr("钱包为非确定性钱包，没有助记词");
    return true;
  }

  epee::wipeable_string seed_pass;
  uint64_t birthday = 0;
  bool is_encrypted = false;
  if (encrypted)
  {
    auto pwd_container = password_prompter(tr("请输入可选的种子偏移密码短语；留空则显示原始助记词"), true);
    if (std::cin.eof() || !pwd_container)
      return true;
    seed_pass = pwd_container->password();
  }

  if (ms_status.multisig_is_active)
    success = m_wallet->get_multisig_seed(seed, seed_pass);
  else if (m_wallet->is_deterministic())
  {
    if (m_wallet->is_polyseed())
    {
      if (as_legacy_seed)
      {
        // We may have a Polyseed in a language that legacy seeds don't support, or have a different name
        // for, thus always give out a "legacy seed" in English to avoid any problems
        success = m_wallet->get_seed(seed, "", true);
      }
      else
      {
        success = m_wallet->get_polyseed(seed, birthday, is_encrypted);
      }
    }
    else
    {
      success = m_wallet->get_seed(seed, seed_pass);
    }
  }

  if (success) 
  {
    print_seed(seed, as_legacy_seed, birthday, is_encrypted);
  }
  else
  {
    fail_msg_writer() << tr("获取助记词失败");
  }
  return true;
}

bool simple_wallet::seed(const std::vector<std::string> &args/* = std::vector<std::string>()*/)
{
  return print_seed(false, false);
}

bool simple_wallet::encrypted_seed(const std::vector<std::string> &args/* = std::vector<std::string>()*/)
{
  return print_seed(true, false);
}

bool simple_wallet::legacy_seed(const std::vector<std::string> &args/* = std::vector<std::string>()*/)
{
  return print_seed(false, true);
}

bool simple_wallet::restore_height(const std::vector<std::string> &args/* = std::vector<std::string>()*/)
{
  success_msg_writer() << m_wallet->get_refresh_from_block_height();
  return true;
}

bool simple_wallet::seed_set_language(const std::vector<std::string> &args/* = std::vector<std::string>()*/)
{
  if (m_wallet->key_on_device())
  {
    fail_msg_writer() << tr("硬件钱包不支持此命令");
    return true;
  }
  if (m_wallet->get_multisig_status().multisig_is_active)
  {
    fail_msg_writer() << tr("钱包是多重签名钱包，没有助记词");
    return true;
  }
  if (m_wallet->watch_only())
  {
    fail_msg_writer() << tr("钱包为仅观察钱包，没有助记词");
    return true;
  }
  CHECK_IF_BACKGROUND_SYNCING("has no seed");

  epee::wipeable_string password;
  {
    SCOPED_WALLET_UNLOCK();

    if (!m_wallet->is_deterministic())
    {
      fail_msg_writer() << tr("钱包为非确定性钱包，没有助记词");
      return true;
    }

    // we need the password, even if ask-password is unset
    if (!pwd_container)
    {
      pwd_container = get_and_verify_password();
      if (pwd_container == boost::none)
      {
        fail_msg_writer() << tr("密码错误");
        return true;
      }
    }
    password = pwd_container->password();
  }

  std::string mnemonic_language = get_mnemonic_language(m_wallet->is_polyseed());
  if (mnemonic_language.empty())
    return true;

  m_wallet->set_seed_language(std::move(mnemonic_language));
  m_wallet->rewrite(m_wallet_file, password);
  return true;
}

bool simple_wallet::change_password(const std::vector<std::string> &args)
{ 
  const auto orig_pwd_container = get_and_verify_password();

  if(orig_pwd_container == boost::none)
  {
    fail_msg_writer() << tr("原密码不正确。");
    return true;
  }

  // prompts for a new password, pass true to verify the password
  const auto pwd_container = default_password_prompter(true);
  if(!pwd_container)
    return true;

  try
  {
    m_wallet->change_password(m_wallet->get_wallet_file(), orig_pwd_container->password(), pwd_container->password());
  }
  catch (const tools::error::wallet_logic_error& e)
  {
    fail_msg_writer() << tr("重新写入钱包时出错：") << e.what();
    return true;
  }

  return true;
}

bool simple_wallet::payment_id(const std::vector<std::string> &args/* = std::vector<std::string>()*/)
{
  LONG_PAYMENT_ID_SUPPORT_CHECK();
}

bool simple_wallet::print_fee_info(const std::vector<std::string> &args/* = std::vector<std::string>()*/)
{
  if (!try_connect_to_daemon())
    return true;
  const bool per_byte = m_wallet->use_fork_rules(HF_VERSION_PER_BYTE_FEE);
  const uint64_t base_fee = m_wallet->get_base_fee();
  const char *base = per_byte ? "byte" : "kB";
  const uint64_t typical_size = per_byte ? 2500 : 13;
  const uint64_t size_granularity = per_byte ? 1 : 1024;
  message_writer() << (boost::format(tr("当前手续费为每 %s %s %s")) % print_money(base_fee) % cryptonote::get_unit(cryptonote::get_default_decimal_point()) % base).str();

  std::vector<uint64_t> fees;
  for (const auto priority : tools::fee_priority_utilities::enums)
  {
    if (priority == fee_priority::Default)
      continue;
    uint64_t mult = m_wallet->get_fee_multiplier(priority);
    fees.push_back(base_fee * typical_size * mult);
  }
  std::vector<std::pair<uint64_t, uint64_t>> blocks;
  try
  {
    uint64_t base_size = typical_size * size_granularity;
    blocks = m_wallet->estimate_backlog(base_size, base_size + size_granularity - 1, fees);
  }
  catch (const std::exception &e)
  {
    fail_msg_writer() << tr("错误：估算交易积压数组大小失败：") << e.what();
    return true;
  }
  if (blocks.size() != 4)
  {
    fail_msg_writer() << tr("错误：估算的交易积压数组大小无效");
    return true;
  }

  for (const auto priority : tools::fee_priority_utilities::enums)
  {
    if (priority == tools::fee_priority::Default)
      continue;

    const auto lower_priority = tools::fee_priority_utilities::decrease(priority);
    const auto lower_priority_index = tools::fee_priority_utilities::as_integral(lower_priority);
    const auto current_priority_index = tools::fee_priority_utilities::as_integral(priority);
    uint64_t nblocks_low = blocks[lower_priority_index].first;
    uint64_t nblocks_high = blocks[lower_priority_index].second;
    if (nblocks_low > 0)
    {
      std::string msg;
      if (priority == m_wallet->get_default_priority() || (m_wallet->get_default_priority() == fee_priority::Default && priority == fee_priority::Normal))
        msg = tr("（当前）");
      uint64_t minutes_low = nblocks_low * DIFFICULTY_TARGET_V2 / 60, minutes_high = nblocks_high * DIFFICULTY_TARGET_V2 / 60;
      if (nblocks_high == nblocks_low)
        message_writer() << (boost::format(tr("优先级 %u 的交易积压：%u 个区块（%u 分钟）%s")) % nblocks_low % minutes_low % current_priority_index % msg).str();
      else
        message_writer() << (boost::format(tr("优先级 %u 的交易积压：%u 至 %u 个区块（%u 至 %u 分钟）")) % nblocks_low % nblocks_high % minutes_low % minutes_high % current_priority_index).str();
    }
    else
      message_writer() << tr("优先级为  的队列为空") << current_priority_index;
  }
  return true;
}

bool simple_wallet::prepare_multisig(const std::vector<std::string> &args)
{
  CHECK_MULTISIG_ENABLED();
  prepare_multisig_main(args, false);
  return true;
}

bool simple_wallet::prepare_multisig_main(const std::vector<std::string> &args, bool called_by_mms)
{
  CHECK_MULTISIG_ENABLED();
  if (m_wallet->key_on_device())
  {
    fail_msg_writer() << tr("硬件钱包不支持此命令");
    return false;
  }
  if (m_wallet->get_multisig_status().multisig_is_active)
  {
    fail_msg_writer() << tr("此钱包已经是多重签名钱包");
    return false;
  }
  if (m_wallet->watch_only())
  {
    fail_msg_writer() << tr("仅观察钱包不能转换为多重签名钱包");
    return false;
  }
  CHECK_IF_BACKGROUND_SYNCING("cannot be made multisig");

  if(m_wallet->get_num_transfer_details())
  {
    fail_msg_writer() << tr("此钱包以前已经使用过，请使用新钱包创建多重签名钱包");
    return false;
  }

  SCOPED_WALLET_UNLOCK_ON_BAD_PASSWORD(return false;);

  std::string multisig_info = m_wallet->get_multisig_first_kex_msg();
  success_msg_writer() << multisig_info;
  success_msg_writer() << tr("将此多重签名信息发送给所有其他参与者，然后使用其他参与者的多重签名信息执行 make_multisig <threshold> <info1> [<info2>...]");
  success_msg_writer() << tr("其中包含私有查看密钥，只能透露给该多重签名钱包的参与者。");

  if (called_by_mms)
  {
    get_message_store().process_wallet_created_data(get_multisig_wallet_state(), mms::message_type::key_set, multisig_info);
  }

  return true;
}

bool simple_wallet::make_multisig(const std::vector<std::string> &args)
{
  CHECK_MULTISIG_ENABLED();
  make_multisig_main(args, false);
  return true;
}

bool simple_wallet::make_multisig_main(const std::vector<std::string> &args, bool called_by_mms)
{
  CHECK_MULTISIG_ENABLED();
  if (m_wallet->key_on_device())
  {
    fail_msg_writer() << tr("硬件钱包不支持此命令");
    return false;
  }
  if (m_wallet->get_multisig_status().multisig_is_active)
  {
    fail_msg_writer() << tr("此钱包已经是多重签名钱包");
    return false;
  }
  if (m_wallet->watch_only())
  {
    fail_msg_writer() << tr("仅观察钱包不能转换为多重签名钱包");
    return false;
  }
  CHECK_IF_BACKGROUND_SYNCING("cannot be made multisig");

  if(m_wallet->get_num_transfer_details())
  {
    fail_msg_writer() << tr("此钱包以前已经使用过，请使用新钱包创建多重签名钱包");
    return false;
  }

  if (args.size() < 2)
  {
    PRINT_USAGE(USAGE_MAKE_MULTISIG);
    return false;
  }

  // parse threshold
  uint32_t threshold;
  if (!string_tools::get_xtype_from_string(threshold, args[0]))
  {
    fail_msg_writer() << tr("阈值无效");
    return false;
  }

  const auto orig_pwd_container = get_and_verify_password();
  if(orig_pwd_container == boost::none)
  {
    fail_msg_writer() << tr("原密码不正确。");
    return false;
  }

  LOCK_IDLE_SCOPE();

  try
  {
    auto local_args = args;
    local_args.erase(local_args.begin());
    std::string multisig_extra_info = m_wallet->make_multisig(orig_pwd_container->password(), local_args, threshold);
    if (!m_wallet->get_multisig_status().is_ready)
    {
      success_msg_writer() << tr("还需要执行下一步");
      success_msg_writer() << multisig_extra_info;
      success_msg_writer() << tr("将此多重签名信息发送给所有其他参与者，然后使用其他参与者的信息执行 exchange_multisig_keys <info1> [<info2>...]");
      if (called_by_mms)
      {
        get_message_store().process_wallet_created_data(get_multisig_wallet_state(), mms::message_type::additional_key_set, multisig_extra_info);
      }
      return true;
    }
  }
  catch (const std::exception &e)
  {
    fail_msg_writer() << tr("创建多重签名钱包错误：") << e.what();
    return false;
  }

  const multisig::multisig_account_status ms_status{m_wallet->get_multisig_status()};
  if (!ms_status.multisig_is_active)
  {
    fail_msg_writer() << tr("创建多重签名钱包错误：新钱包不是多重签名钱包");
    return false;
  }
  success_msg_writer() << std::to_string(ms_status.threshold) << "/" << ms_status.total << tr(" 多重签名地址：")
      << m_wallet->get_account().get_public_address_str(m_wallet->nettype());

  return true;
}

bool simple_wallet::exchange_multisig_keys(const std::vector<std::string> &args)
{
  CHECK_MULTISIG_ENABLED();
  bool force_update_use_with_caution = false;

  auto local_args = args;
  if (args.size() >= 1 && local_args[0] == "force-update-use-with-caution")
  {
    force_update_use_with_caution = true;
    local_args.erase(local_args.begin());
  }

  exchange_multisig_keys_main(local_args, force_update_use_with_caution, false);
  return true;
}

bool simple_wallet::exchange_multisig_keys_main(const std::vector<std::string> &args,
  const bool force_update_use_with_caution,
  const bool called_by_mms) {
    CHECK_MULTISIG_ENABLED();
    const multisig::multisig_account_status ms_status{m_wallet->get_multisig_status()};
    if (m_wallet->key_on_device())
    {
      fail_msg_writer() << tr("硬件钱包不支持此命令");
      return false;
    }
    if (!ms_status.multisig_is_active)
    {
      fail_msg_writer() << tr("此钱包不是多重签名钱包");
      return false;
    }
    if (ms_status.is_ready)
    {
      fail_msg_writer() << tr("此钱包已经完成多重签名设置");
      return false;
    }

    const auto orig_pwd_container = get_and_verify_password();
    if(orig_pwd_container == boost::none)
    {
      fail_msg_writer() << tr("原密码不正确。");
      return false;
    }

    LOCK_IDLE_SCOPE();

    try
    {
      std::string multisig_extra_info = m_wallet->exchange_multisig_keys(orig_pwd_container->password(), args, force_update_use_with_caution);
      if (!m_wallet->get_multisig_status().is_ready)
      {
        message_writer() << tr("还需要执行下一步");
        message_writer() << multisig_extra_info;
        message_writer() << tr("将此多重签名信息发送给所有其他参与者，然后使用其他参与者的信息执行 exchange_multisig_keys <info1> [<info2>...]");
        if (called_by_mms)
        {
          get_message_store().process_wallet_created_data(get_multisig_wallet_state(), mms::message_type::additional_key_set, multisig_extra_info);
        }
        return true;
      } else {
        const multisig::multisig_account_status ms_status_new{m_wallet->get_multisig_status()};
        success_msg_writer() << tr("多重签名钱包创建成功。当前钱包类型：") << ms_status_new.threshold << "/" << ms_status_new.total;
        success_msg_writer() << tr("多重签名地址：") << m_wallet->get_account().get_public_address_str(m_wallet->nettype());
      }
    }
    catch (const std::exception &e)
    {
      fail_msg_writer() << tr("执行多重签名密钥交换失败：") << e.what();
      return false;
    }

    return true;
}

bool simple_wallet::export_multisig(const std::vector<std::string> &args)
{
  CHECK_MULTISIG_ENABLED();
  export_multisig_main(args, false);
  return true;
}

bool simple_wallet::export_multisig_main(const std::vector<std::string> &args, bool called_by_mms)
{
  CHECK_MULTISIG_ENABLED();
  const multisig::multisig_account_status ms_status{m_wallet->get_multisig_status()};
  if (m_wallet->key_on_device())
  {
    fail_msg_writer() << tr("硬件钱包不支持此命令");
    return false;
  }
  if (!ms_status.multisig_is_active)
  {
    fail_msg_writer() << tr("此钱包不是多重签名钱包");
    return false;
  }
  if (!ms_status.is_ready)
  {
    fail_msg_writer() << tr("此多重签名钱包尚未完成设置");
    return false;
  }
  if (args.size() != 1)
  {
    PRINT_USAGE(USAGE_EXPORT_MULTISIG_INFO);
    return false;
  }

  const std::string filename = args[0];
  if (!called_by_mms && m_wallet->confirm_export_overwrite() && !check_file_overwrite(filename))
    return true;

  SCOPED_WALLET_UNLOCK_ON_BAD_PASSWORD(return false;);

  try
  {
    cryptonote::blobdata ciphertext = m_wallet->export_multisig();

    if (called_by_mms)
    {
      get_message_store().process_wallet_created_data(get_multisig_wallet_state(), mms::message_type::multisig_sync_data, ciphertext);
    }
    else
    {
      bool r = m_wallet->save_to_file(filename, ciphertext);
      if (!r)
      {
        fail_msg_writer() << tr("保存文件失败 ") << filename;
        return false;
      }
    }
  }
  catch (const std::exception &e)
  {
    LOG_ERROR("导出多重签名信息失败：" << e.what());
    fail_msg_writer() << tr("导出多重签名信息失败：") << e.what();
    return false;
  }

  success_msg_writer() << tr("多重签名信息已导出到 ") << filename;
  return true;
}

bool simple_wallet::import_multisig(const std::vector<std::string> &args)
{
  CHECK_MULTISIG_ENABLED();
  import_multisig_main(args, false);
  return true;
}

bool simple_wallet::import_multisig_main(const std::vector<std::string> &args, bool called_by_mms)
{
  CHECK_MULTISIG_ENABLED();
  const multisig::multisig_account_status ms_status{m_wallet->get_multisig_status()};

  if (m_wallet->key_on_device())
  {
    fail_msg_writer() << tr("硬件钱包不支持此命令");
    return false;
  }
  if (!ms_status.multisig_is_active)
  {
    fail_msg_writer() << tr("此钱包不是多重签名钱包");
    return false;
  }
  if (!ms_status.is_ready)
  {
    fail_msg_writer() << tr("此多重签名钱包尚未完成设置");
    return false;
  }
  if (args.size() + 1 < ms_status.threshold)
  {
    PRINT_USAGE(USAGE_IMPORT_MULTISIG_INFO);
    return false;
  }

  std::vector<cryptonote::blobdata> info;
  for (size_t n = 0; n < args.size(); ++n)
  {
    if (called_by_mms)
    {
      info.push_back(args[n]);
    }
    else
    {
      const std::string &filename = args[n];
      std::string data;
      bool r = m_wallet->load_from_file(filename, data);
      if (!r)
      {
        fail_msg_writer() << tr("读取文件失败 ") << filename;
        return false;
      }
      info.push_back(std::move(data));
    }
  }

  SCOPED_WALLET_UNLOCK_ON_BAD_PASSWORD(return false;);

  // all read and parsed, actually import
  try
  {
    m_in_manual_refresh.store(true, std::memory_order_relaxed);
    const epee::scope_guard scope_exit_handler([&](){m_in_manual_refresh.store(false, std::memory_order_relaxed);});
    size_t n_outputs = m_wallet->import_multisig(info);
    // Clear line "Height xxx of xxx"
    std::cout << "\r                                                                \r";
    success_msg_writer() << tr("多重签名信息已导入。已更新输出数量：") << n_outputs;
  }
  catch (const std::exception &e)
  {
    fail_msg_writer() << tr("导入多重签名信息失败：") << e.what();
    return false;
  }
  if (m_wallet->is_trusted_daemon())
  {
    try
    {
      m_wallet->rescan_spent();
    }
    catch (const std::exception &e)
    {
      message_writer() << tr("导入多重签名信息后更新已花费状态失败：") << e.what();
      return false;
    }
  }
  else
  {
    message_writer() << tr("不受信任的守护进程，已花费状态可能不正确。请使用受信任的守护进程并运行“rescan_spent”");
    return false;
  }
  return true;
}

bool simple_wallet::accept_loaded_tx(const tools::wallet2::multisig_tx_set &txs)
{
  std::string extra_message;
  return accept_loaded_tx([&txs](){return txs.m_ptx.size();}, [&txs](size_t n)->const tools::wallet2::tx_construction_data&{return txs.m_ptx[n].construction_data;}, extra_message);
}

bool simple_wallet::sign_multisig(const std::vector<std::string> &args)
{
  CHECK_MULTISIG_ENABLED();
  sign_multisig_main(args, false);
  return true;
}

bool simple_wallet::sign_multisig_main(const std::vector<std::string> &args, bool called_by_mms)
{
  CHECK_MULTISIG_ENABLED();
  const multisig::multisig_account_status ms_status{m_wallet->get_multisig_status()};\

  if (m_wallet->key_on_device())
  {
    fail_msg_writer() << tr("硬件钱包不支持此命令");
    return false;
  }
  if (!ms_status.multisig_is_active)
  {
    fail_msg_writer() << tr("此钱包不是多重签名钱包");
    return false;
  }
  if (!ms_status.is_ready)
  {
    fail_msg_writer() << tr("此多重签名钱包尚未完成设置");
    return false;
  }
  if (args.size() != 1)
  {
    PRINT_USAGE(USAGE_SIGN_MULTISIG);
    return false;
  }

  SCOPED_WALLET_UNLOCK_ON_BAD_PASSWORD(return false;);

  std::string filename = args[0];
  std::vector<crypto::hash> txids;
  uint32_t signers = 0;
  try
  {
    if (called_by_mms)
    {
      tools::wallet2::multisig_tx_set exported_txs;
      std::string ciphertext;
      bool r = m_wallet->load_multisig_tx(args[0], exported_txs, [&](const tools::wallet2::multisig_tx_set &tx){ signers = tx.m_signers.size(); return accept_loaded_tx(tx); });
      if (r)
      {
        r = m_wallet->sign_multisig_tx(exported_txs, txids);
      }
      if (r)
      {
        ciphertext = m_wallet->save_multisig_tx(exported_txs);
        if (ciphertext.empty())
        {
          r = false;
        }
      }
      if (r)
      {
        mms::message_type message_type = mms::message_type::fully_signed_tx;
        if (txids.empty())
        {
          message_type = mms::message_type::partially_signed_tx;
        }
        get_message_store().process_wallet_created_data(get_multisig_wallet_state(), message_type, ciphertext);
        filename = "MMS";   // for the messages below
      }
      else
      {
        fail_msg_writer() << tr("签署多重签名交易失败");
        return false;
      }
    }
    else
    {
      bool r = m_wallet->sign_multisig_tx_from_file(filename, txids, [&](const tools::wallet2::multisig_tx_set &tx){ signers = tx.m_signers.size(); return accept_loaded_tx(tx); });
      if (!r)
      {
        fail_msg_writer() << tr("签署多重签名交易失败");
        return false;
      }
    }
  }
  catch (const tools::error::multisig_export_needed& e)
  {
    fail_msg_writer() << tr("多重签名错误：") << e.what();
    return false;
  }
  catch (const std::exception &e)
  {
    fail_msg_writer() << tr("签署多重签名交易失败: ") << e.what();
    return false;
  }

  if (txids.empty())
  {
    uint32_t signers_needed = ms_status.threshold - signers - 1;
    success_msg_writer(true) << tr("交易已成功签名并保存到文件 ") << filename << ", "
        << signers_needed << " more signer(s) needed";
    return true;
  }
  else
  {
    std::string txids_as_text;
    for (const auto &txid: txids)
    {
      if (!txids_as_text.empty())
        txids_as_text += (", ");
      txids_as_text += epee::string_tools::pod_to_hex(txid);
    }
    success_msg_writer(true) << tr("交易已成功签名并保存到文件 ") << filename << ", txid " << txids_as_text;
    success_msg_writer(true) << tr("可以使用 submit_multisig 将其广播到网络");
  }
  return true;
}

bool simple_wallet::submit_multisig(const std::vector<std::string> &args)
{
  CHECK_MULTISIG_ENABLED();
  submit_multisig_main(args, false);
  return true;
}

bool simple_wallet::submit_multisig_main(const std::vector<std::string> &args, bool called_by_mms)
{
  CHECK_MULTISIG_ENABLED();
  const multisig::multisig_account_status ms_status{m_wallet->get_multisig_status()};

  if (m_wallet->key_on_device())
  {
    fail_msg_writer() << tr("硬件钱包不支持此命令");
    return false;
  }
  if (!ms_status.multisig_is_active)
  {
    fail_msg_writer() << tr("此钱包不是多重签名钱包");
    return false;
  }
  if (!ms_status.is_ready)
  {
    fail_msg_writer() << tr("此多重签名钱包尚未完成设置");
    return false;
  }
  if (args.size() != 1)
  {
    PRINT_USAGE(USAGE_SUBMIT_MULTISIG);
    return false;
  }

  if (!try_connect_to_daemon())
    return false;

  SCOPED_WALLET_UNLOCK_ON_BAD_PASSWORD(return false;);

  std::string filename = args[0];
  try
  {
    tools::wallet2::multisig_tx_set txs;
    if (called_by_mms)
    {
      bool r = m_wallet->load_multisig_tx(args[0], txs, [&](const tools::wallet2::multisig_tx_set &tx){ return accept_loaded_tx(tx); });
      if (!r)
      {
        fail_msg_writer() << tr("从 MMS 加载多重签名交易失败");
        return false;
      }
    }
    else
    {
      bool r = m_wallet->load_multisig_tx_from_file(filename, txs, [&](const tools::wallet2::multisig_tx_set &tx){ return accept_loaded_tx(tx); });
      if (!r)
      {
        fail_msg_writer() << tr("从文件加载多重签名交易失败");
        return false;
      }
    }
    if (txs.m_signers.size() < ms_status.threshold)
    {
      fail_msg_writer() << (boost::format(tr("多重签名交易目前仅由 %u 个签名者签名，还需要 %u 个签名"))
          % txs.m_signers.size() % (ms_status.threshold - txs.m_signers.size())).str();
      return false;
    }

    // actually commit the transactions
    commit_or_save(txs.m_ptx, /* do_not_relay */ false);
  }
  catch (const std::exception &e)
  {
    handle_transfer_exception(std::current_exception(), m_wallet->is_trusted_daemon());
  }
  catch (...)
  {
    LOG_ERROR("未知错误");
    fail_msg_writer() << tr("未知错误");
    return false;
  }

  return true;
}

bool simple_wallet::export_raw_multisig(const std::vector<std::string> &args)
{
  CHECK_MULTISIG_ENABLED();
  const multisig::multisig_account_status ms_status{m_wallet->get_multisig_status()};

  if (m_wallet->key_on_device())
  {
    fail_msg_writer() << tr("硬件钱包不支持此命令");
    return true;
  }
  if (!ms_status.multisig_is_active)
  {
    fail_msg_writer() << tr("此钱包不是多重签名钱包");
    return true;
  }
  if (!ms_status.is_ready)
  {
    fail_msg_writer() << tr("此多重签名钱包尚未完成设置");
    return true;
  }
  if (args.size() != 1)
  {
    PRINT_USAGE(USAGE_EXPORT_RAW_MULTISIG_TX);
    return true;
  }

  std::string filename = args[0];
  if (m_wallet->confirm_export_overwrite() && !check_file_overwrite(filename))
    return true;

  SCOPED_WALLET_UNLOCK();

  try
  {
    tools::wallet2::multisig_tx_set txs;
    bool r = m_wallet->load_multisig_tx_from_file(filename, txs, [&](const tools::wallet2::multisig_tx_set &tx){ return accept_loaded_tx(tx); });
    if (!r)
    {
      fail_msg_writer() << tr("从文件加载多重签名交易失败");
      return true;
    }
    if (txs.m_signers.size() < ms_status.threshold)
    {
      fail_msg_writer() << (boost::format(tr("多重签名交易目前仅由 %u 个签名者签名，还需要 %u 个签名"))
          % txs.m_signers.size() % (ms_status.threshold - txs.m_signers.size())).str();
      return true;
    }

    // save the transactions
    std::string filenames;
    for (auto &ptx: txs.m_ptx)
    {
      const crypto::hash txid = cryptonote::get_transaction_hash(ptx.tx);
      const std::string filename = std::string("raw_multisig_monero_tx_") + epee::string_tools::pod_to_hex(txid);
      if (!filenames.empty())
        filenames += ", ";
      filenames += filename;
      if (!m_wallet->save_to_file(filename, cryptonote::tx_to_blob(ptx.tx)))
      {
        fail_msg_writer() << tr("导出多重签名交易到文件失败：") << filename;
        return true;
      }
    }
    success_msg_writer() << tr("已保存导出的多重签名交易文件：") << filenames;
  }
  catch (const std::exception& e)
  {
    LOG_ERROR("意外错误：" << e.what());
    fail_msg_writer() << tr("意外错误：") << e.what();
  }
  catch (...)
  {
    LOG_ERROR("Unknown error");
    fail_msg_writer() << tr("未知错误");
  }

  return true;
}

bool simple_wallet::print_ring(const std::vector<std::string> &args)
{
  crypto::key_image key_image;
  crypto::hash txid;
  if (args.size() != 1)
  {
    PRINT_USAGE(USAGE_PRINT_RING);
    return true;
  }

  if (!epee::string_tools::hex_to_pod(args[0], key_image))
  {
    fail_msg_writer() << tr("无效的密钥镜像");
    return true;
  }
  // this one will always work, they're all 32 byte hex
  if (!epee::string_tools::hex_to_pod(args[0], txid))
  {
    fail_msg_writer() << tr("无效的交易 ID");
    return true;
  }

  std::vector<uint64_t> ring;
  std::vector<std::pair<crypto::key_image, std::vector<uint64_t>>> rings;
  try
  {
    if (m_wallet->get_ring(key_image, ring))
      rings.push_back({key_image, ring});
    else if (!m_wallet->get_rings(txid, rings))
    {
      fail_msg_writer() << tr("密钥镜像尚未花费，或使用环大小 1 花费");
      return true;
    }

    for (const auto &ring: rings)
    {
      std::stringstream str;
      for (const auto &x: ring.second)
        str << x<< " ";
      // do NOT translate this "absolute" below, the lin can be used as input to set_ring
      success_msg_writer() << epee::string_tools::pod_to_hex(ring.first) <<  " absolute " << str.str();
    }
  }
  catch (const std::exception &e)
  {
    fail_msg_writer() << tr("获取密钥镜像环失败：") << e.what();
  }

  return true;
}

bool simple_wallet::set_ring(const std::vector<std::string> &args)
{
  crypto::key_image key_image;

  // try filename first
  if (args.size() == 1)
  {
    if (!epee::file_io_utils::is_file_exist(args[0]))
    {
      fail_msg_writer() << tr("文件不存在");
      return true;
    }

    char str[4096];
    std::unique_ptr<FILE, tools::close_file> f(fopen(args[0].c_str(), "r"));
    if (f)
    {
      while (!feof(f.get()))
      {
        if (!fgets(str, sizeof(str), f.get()))
          break;
        const size_t len = strlen(str);
        if (len > 0 && str[len - 1] == '\n')
          str[len - 1] = 0;
        if (!str[0])
          continue;
        char key_image_str[65], type_str[9];
        int read_after_key_image = 0, read = 0;
        int fields = sscanf(str, "%64[abcdefABCDEF0123456789] %n%8s %n", key_image_str, &read_after_key_image, type_str, &read);
        if (fields != 2)
        {
          fail_msg_writer() << tr("无效的环指定：") << str;
          continue;
        }
        key_image_str[64] = 0;
        type_str[8] = 0;
        crypto::key_image key_image;
        if (read_after_key_image == 0 || !epee::string_tools::hex_to_pod(key_image_str, key_image))
        {
          fail_msg_writer() << tr("无效的密钥镜像: ") << str;
          continue;
        }
        if (read == read_after_key_image+8 || (strcmp(type_str, "absolute") && strcmp(type_str, "relative")))
        {
          fail_msg_writer() << tr("无效的环类型，应为相对或绝对：") << str;
          continue;
        }
        bool relative = !strcmp(type_str, "relative");
        if (read < 0 || (size_t)read > strlen(str))
        {
          fail_msg_writer() << tr("读取行错误：") << str;
          continue;
        }
        bool valid = true;
        std::vector<uint64_t> ring;
        const char *ptr = str + read;
        while (*ptr)
        {
          unsigned long offset;
          int elements = sscanf(ptr, "%lu %n", &offset, &read);
          if (elements == 0 || read <= 0 || (size_t)read > strlen(str))
          {
            fail_msg_writer() << tr("读取行错误：") << str;
            valid = false;
            break;
          }
          ring.push_back(offset);
          ptr += read;
        }
        if (!valid)
          continue;
        if (ring.empty())
        {
          fail_msg_writer() << tr("无效的环：") << str;
          continue;
        }
        if (relative)
        {
          for (size_t n = 1; n < ring.size(); ++n)
          {
            if (ring[n] <= 0)
            {
              fail_msg_writer() << tr("无效的相对环：") << str;
              valid = false;
              break;
            }
          }
        }
        else
        {
          for (size_t n = 1; n < ring.size(); ++n)
          {
            if (ring[n] <= ring[n-1])
            {
              fail_msg_writer() << tr("无效的绝对环：") << str;
              valid = false;
              break;
            }
          }
        }
        if (!valid)
          continue;
        if (!m_wallet->set_ring(key_image, ring, relative))
          fail_msg_writer() << tr("为密钥镜像设置环失败：") << key_image << ". " << tr("继续执行。");
      }
      f.reset();
    }
    return true;
  }

  if (args.size() < 3)
  {
    PRINT_USAGE(USAGE_SET_RING);
    return true;
  }

  if (!epee::string_tools::hex_to_pod(args[0], key_image))
  {
    fail_msg_writer() << tr("无效的密钥镜像");
    return true;
  }

  bool relative;
  if (args[1] == "absolute")
  {
    relative = false;
  }
  else if (args[1] == "relative")
  {
    relative = true;
  }
  else
  {
    fail_msg_writer() << tr("缺少 absolute 或 relative 关键字");
    return true;
  }

  std::vector<uint64_t> ring;
  for (size_t n = 2; n < args.size(); ++n)
  {
    ring.resize(ring.size() + 1);
    if (!string_tools::get_xtype_from_string(ring.back(), args[n]))
    {
      fail_msg_writer() << tr("索引无效：必须是严格大于 0 的无符号整数");
      return true;
    }
    if (relative)
    {
      if (ring.size() > 1 && !ring.back())
      {
        fail_msg_writer() << tr("索引无效：必须是严格大于 0 的无符号整数");
        return true;
      }
      uint64_t sum = 0;
      for (uint64_t out: ring)
      {
        if (out > std::numeric_limits<uint64_t>::max() - sum)
        {
          fail_msg_writer() << tr("索引无效：索引发生回绕");
          return true;
        }
        sum += out;
      }
    }
    else
    {
      if (ring.size() > 1 && ring[ring.size() - 2] >= ring[ring.size() - 1])
      {
        fail_msg_writer() << tr("索引无效：索引必须严格递增");
        return true;
      }
    }
  }
  if (!m_wallet->set_ring(key_image, ring, relative))
  {
    fail_msg_writer() << tr("设置环失败");
    return true;
  }

  return true;
}

bool simple_wallet::unset_ring(const std::vector<std::string> &args)
{
  crypto::hash txid;
  std::vector<crypto::key_image> key_images;

  if (args.size() < 1)
  {
    PRINT_USAGE(USAGE_UNSET_RING);
    return true;
  }

  key_images.resize(args.size());
  for (size_t i = 0; i < args.size(); ++i)
  {
    if (!epee::string_tools::hex_to_pod(args[i], key_images[i]))
    {
      fail_msg_writer() << tr("无效的密钥镜像或交易 ID");
      return true;
    }
  }
  static_assert(sizeof(crypto::hash) == sizeof(crypto::key_image), "hash and key_image must have the same size");
  memcpy(&txid, &key_images[0], sizeof(txid));

  if (!m_wallet->unset_ring(key_images) && !m_wallet->unset_ring(txid))
  {
    fail_msg_writer() << tr("取消环设置失败");
    return true;
  }

  return true;
}

bool simple_wallet::save_known_rings(const std::vector<std::string> &args)
{
  fail_msg_writer() << tr("save_known_rings 已废弃");
  return true;
}

bool simple_wallet::freeze_thaw(const std::vector<std::string> &args, bool freeze)
{
  CHECK_IF_BACKGROUND_SYNCING("cannot freeze/thaw");
  if (args.empty())
  {
    fail_msg_writer() << boost::format(tr("用法：%s <key_image>|<pubkey>")) % (freeze ? "freeze" : "thaw");
    return true;
  }
  crypto::key_image ki;
  if (!epee::string_tools::hex_to_pod(args[0], ki))
  {
    fail_msg_writer() << tr("解析密钥镜像失败");
    return true;
  }
  try
  {
    if (freeze)
      m_wallet->freeze(ki);
    else
      m_wallet->thaw(ki);
  }
  catch (const std::exception &e)
  {
    fail_msg_writer() << e.what();
    return true;
  }

  return true;
}

bool simple_wallet::freeze(const std::vector<std::string> &args)
{
  return freeze_thaw(args, true);
}

bool simple_wallet::thaw(const std::vector<std::string> &args)
{
  return freeze_thaw(args, false);
}

bool simple_wallet::frozen(const std::vector<std::string> &args)
{
  CHECK_IF_BACKGROUND_SYNCING("cannot see frozen key images");
  if (args.empty())
  {
    size_t ntd = m_wallet->get_num_transfer_details();
    for (size_t i = 0; i < ntd; ++i)
    {
      if (!m_wallet->frozen(i))
        continue;
      const tools::wallet2::transfer_details &td = m_wallet->get_transfer_details(i);
      message_writer() << tr("已冻结：") << td.m_key_image << " " << cryptonote::print_money(td.amount());
    }
  }
  else
  {
    crypto::key_image ki;
    if (!epee::string_tools::hex_to_pod(args[0], ki))
    {
      fail_msg_writer() << tr("解析密钥镜像失败");
      return true;
    }
    if (m_wallet->frozen(ki))
      message_writer() << tr("已冻结：") << ki;
    else
      message_writer() << tr("未冻结：") << ki;
  }
  return true;
}

bool simple_wallet::lock(const std::vector<std::string> &args)
{
  m_locked = true;
  check_for_inactivity_lock(true);
  return true;
}

bool simple_wallet::net_stats(const std::vector<std::string> &args)
{
  message_writer() << std::to_string(m_wallet->get_bytes_sent()) + tr(" 字节已发送");
  message_writer() << std::to_string(m_wallet->get_bytes_received()) + tr(" 字节已接收");
  return true;
}

bool simple_wallet::public_nodes(const std::vector<std::string> &args)
{
  try
  {
    auto nodes = m_wallet->get_public_nodes(false);
    if (nodes.empty())
    {
      fail_msg_writer() << tr("没有已知的公共节点");
      return true;
    }

    const uint64_t now = time(NULL);
    message_writer() << boost::format("%32s %16s") % tr("address") % tr("最后出现");
    for (const auto &node: nodes)
    {
      const std::string last_seen = node.last_seen == 0 ? tr("从未") : tools::get_human_readable_timespan(std::chrono::seconds(now - node.last_seen));
      std::string host = node.host + ":" + std::to_string(node.rpc_port);
      message_writer() << boost::format("%32s %16s") % host % last_seen;
    }
  }
  catch (const std::exception &e)
  {
    fail_msg_writer() << tr("获取公共节点列表失败：") << e.what();
  }
  message_writer(console_color_red, true) << tr("这些节点大多可能是监视节点。除非通过 Tor 或 I2P 连接，否则不建议使用");
  return true;
}

bool simple_wallet::welcome(const std::vector<std::string> &args)
{
  message_writer() << tr("欢迎使用 Monero，这是一种注重隐私的加密货币。");
  message_writer() << "";
  message_writer() << tr("Monero 与比特币一样，是一种加密货币，也就是数字货币。");
  message_writer() << tr("与比特币不同，Monero 的交易和余额默认保持私密，不会对所有人公开。");
  message_writer() << tr("不过，您可以选择向指定人员公开这些信息。");
  message_writer() << "";
  message_writer() << tr("Monero 会在区块链上保护您的隐私。虽然 Monero 一直在持续改进，");
  message_writer() << tr("但任何隐私技术都不可能做到 100% 完美，Monero 也不例外。");
  message_writer() << tr("Monero 无法保护您免受恶意软件攻击，而且面对强大的攻击者时，隐私保护效果可能不如预期。");
  message_writer() << tr("未来可能发现 Monero 的缺陷，也可能出现针对隐私保护机制的攻击，试图窥探");
  message_writer() << tr("Monero 提供的部分隐私层。请保持谨慎，并采用纵深防御。");
  message_writer() << "";
  message_writer() << tr("欢迎使用 Monero 和金融隐私功能。更多信息请访问 https://GetMonero.org");
  return true;
}

bool simple_wallet::version(const std::vector<std::string> &args)
{
  message_writer() << "Monero '" << MONERO_RELEASE_NAME << "' (v" << MONERO_VERSION_FULL << ")";
  return true;
}

bool simple_wallet::clear(const std::vector<std::string> &args)
{
  PAUSE_READLINE();
  tools::clear_screen();
  return true;
}

bool simple_wallet::on_unknown_command(const std::vector<std::string> &args)
{
  if (args[0] == "exit" || args[0] == "q") // backward compat
    return false;
  fail_msg_writer() << boost::format(tr("未知命令“%s”，请尝试输入“help”")) % args.front();
  return true;
}

bool simple_wallet::on_empty_command()
{
  return true;
}

bool simple_wallet::on_cancelled_command()
{
  check_for_inactivity_lock(false);
  return true;
}

bool simple_wallet::cold_sign_tx(const std::vector<tools::wallet2::pending_tx>& ptx_vector, tools::wallet2::signed_tx_set &exported_txs, std::vector<cryptonote::address_parse_info> &dsts_info, std::function<bool(const tools::wallet2::signed_tx_set &)> accept_func)
{
  std::vector<std::string> tx_aux;

  message_writer(console_color_white, false) << tr("请在设备上确认交易");

  m_wallet->cold_sign_tx(ptx_vector, exported_txs, dsts_info, tx_aux);

  if (accept_func && !accept_func(exported_txs))
  {
    MERROR("Transactions rejected by callback");
    return false;
  }

  // aux info
  m_wallet->cold_tx_aux_import(exported_txs.ptx, tx_aux);

  // import key images
  return m_wallet->import_key_images(exported_txs, 0, true);
}

bool simple_wallet::show_qr_code(const std::vector<std::string> &args)
{
  uint32_t subaddress_index = 0;
  if (args.size() >= 1)
  {
    if (!string_tools::get_xtype_from_string(subaddress_index, args[0]))
    {
      fail_msg_writer() << tr("索引无效：必须是无符号整数");
      return true;
    }
    if (subaddress_index >= m_wallet->get_num_subaddresses(m_current_subaddress_account))
    {
      fail_msg_writer() << tr("<subaddress_index> 超出范围");
      return true;
    }
  }

#ifdef _WIN32
#define PRINT_UTF8(pre, x) std::wcout << pre ## x
#define WTEXTON() _setmode(_fileno(stdout), _O_WTEXT)
#define WTEXTOFF() _setmode(_fileno(stdout), _O_TEXT)
#else
#define PRINT_UTF8(pre, x) std::cout << x
#define WTEXTON()
#define WTEXTOFF()
#endif

  WTEXTON();
  try
  {
    const std::string address = "monero:" + m_wallet->get_subaddress_as_str({m_current_subaddress_account, subaddress_index});
    const qrcodegen::QrCode qr = qrcodegen::QrCode::encodeText(address.c_str(), qrcodegen::QrCode::Ecc::LOW);
    for (int y = -2; y < qr.getSize() + 2; y+=2)
    {
      for (int x = -2; x < qr.getSize() + 2; x++)
      {
        if (qr.getModule(x, y) && qr.getModule(x, y + 1))
          PRINT_UTF8(L, "\u2588");
        else if (qr.getModule(x, y) && !qr.getModule(x, y + 1))
          PRINT_UTF8(L, "\u2580");
        else if (!qr.getModule(x, y) && qr.getModule(x, y + 1))
          PRINT_UTF8(L, "\u2584");
        else
          PRINT_UTF8(L, " ");
      }
      PRINT_UTF8(, std::endl);
    }
  }
  catch (const std::length_error&)
  {
    fail_msg_writer() << tr("生成二维码失败，输入内容过大");
  }
  WTEXTOFF();
  return true;
}

bool simple_wallet::set_always_confirm_transfers(const std::vector<std::string> &args/* = std::vector<std::string>()*/)
{
  const auto pwd_container = get_and_verify_password();
  if (pwd_container)
  {
    parse_bool_and_use(args[1], [&](bool r) {
      m_wallet->always_confirm_transfers(r);
      m_wallet->rewrite(m_wallet_file, pwd_container->password());
    });
  }
  return true;
}

bool simple_wallet::set_print_ring_members(const std::vector<std::string> &args/* = std::vector<std::string>()*/)
{
  const auto pwd_container = get_and_verify_password();
  if (pwd_container)
  {
    parse_bool_and_use(args[1], [&](bool r) {
      m_wallet->print_ring_members(r);
      m_wallet->rewrite(m_wallet_file, pwd_container->password());
    });
  }
  return true;
}

bool simple_wallet::set_store_tx_info(const std::vector<std::string> &args/* = std::vector<std::string>()*/)
{
  if (m_wallet->watch_only())
  {
    fail_msg_writer() << tr("仅观察钱包不能转账");
    return true;
  }
 
  const auto pwd_container = get_and_verify_password();
  if (pwd_container)
  {
    parse_bool_and_use(args[1], [&](bool r) {
      m_wallet->store_tx_info(r);
      m_wallet->rewrite(m_wallet_file, pwd_container->password());
    });
  }
  return true;
}

bool simple_wallet::set_default_priority(const std::vector<std::string> &args/* = std::vector<std::string>()*/)
{
  uint32_t priority = 0;
  try
  {
    if (strchr(args[1].c_str(), '-'))
    {
      fail_msg_writer() << tr("优先级必须为 0、1、2、3、4，或者为以下值之一：") << join_priority_strings(", ");
      return true;
    }
    if (args[1] == "0")
    {
      priority = 0;
    }
    else
    {
      bool found = false;
      for (size_t n = 0; n < allowed_priority_strings.size(); ++n)
      {
        if (allowed_priority_strings[n] == args[1])
        {
          found = true;
          priority = n;
        }
      }
      if (!found)
      {
        priority = boost::lexical_cast<int>(args[1]);
        if (priority < tools::fee_priority_utilities::as_integral(fee_priority::Unimportant) || priority > tools::fee_priority_utilities::as_integral(fee_priority::Priority))
        {
          fail_msg_writer() << tr("优先级必须为 0、1、2、3、4，或者为以下值之一：") << join_priority_strings(", ");
          return true;
        }
      }
    }
 
    const auto pwd_container = get_and_verify_password();
    if (pwd_container)
    {
      m_wallet->set_default_priority(tools::fee_priority_utilities::from_integral(priority));
      m_wallet->rewrite(m_wallet_file, pwd_container->password());
    }
    return true;
  }
  catch(const boost::bad_lexical_cast &)
  {
    fail_msg_writer() << tr("优先级必须为 0、1、2、3、4，或者为以下值之一：") << join_priority_strings(", ");
    return true;
  }
  catch(...)
  {
    fail_msg_writer() << tr("无法修改默认优先级");
    return true;
  }
}

bool simple_wallet::set_auto_refresh(const std::vector<std::string> &args/* = std::vector<std::string>()*/)
{
  const auto pwd_container = get_and_verify_password();
  if (pwd_container)
  {
    parse_bool_and_use(args[1], [&](bool auto_refresh) {
      m_auto_refresh_enabled.store(false, std::memory_order_relaxed);
      m_wallet->auto_refresh(auto_refresh);
      m_idle_mutex.lock();
      m_auto_refresh_enabled.store(auto_refresh, std::memory_order_relaxed);
      m_idle_cond.notify_one();
      m_idle_mutex.unlock();

      m_wallet->rewrite(m_wallet_file, pwd_container->password());
    });
  }
  return true;
}

bool simple_wallet::set_refresh_type(const std::vector<std::string> &args/* = std::vector<std::string>()*/)
{
  tools::wallet2::RefreshType refresh_type;
  if (!parse_refresh_type(args[1], refresh_type))
  {
    return true;
  }
 
  const auto pwd_container = get_and_verify_password();
  if (pwd_container)
  {
    m_wallet->set_refresh_type(refresh_type);
    m_wallet->rewrite(m_wallet_file, pwd_container->password());
  }
  return true;
}

bool simple_wallet::set_ask_password(const std::vector<std::string> &args/* = std::vector<std::string>()*/)
{
  const auto pwd_container = get_and_verify_password();
  if (pwd_container)
  {
    tools::wallet2::AskPasswordType ask = tools::wallet2::AskPasswordToDecrypt;
    if (args[1] == "never" || args[1] == "0")
      ask = tools::wallet2::AskPasswordNever;
    else if (args[1] == "action" || args[1] == "1")
      ask = tools::wallet2::AskPasswordOnAction;
    else if (args[1] == "encrypt" || args[1] == "decrypt" || args[1] == "2")
      ask = tools::wallet2::AskPasswordToDecrypt;
    else
    {
      fail_msg_writer() << tr("参数无效：必须为 0/never、1/action 或 2/encrypt/decrypt");
      return true;
    }

    const tools::wallet2::AskPasswordType cur_ask = m_wallet->ask_password();
    if (!m_wallet->watch_only())
    {
      if (cur_ask == tools::wallet2::AskPasswordToDecrypt && ask != tools::wallet2::AskPasswordToDecrypt)
        m_wallet->decrypt_keys(pwd_container->password());
      else if (cur_ask != tools::wallet2::AskPasswordToDecrypt && ask == tools::wallet2::AskPasswordToDecrypt)
        m_wallet->encrypt_keys(pwd_container->password());
    }
    m_wallet->ask_password(ask);
    m_wallet->rewrite(m_wallet_file, pwd_container->password());
  }
  return true;
}

bool simple_wallet::set_unit(const std::vector<std::string> &args/* = std::vector<std::string>()*/)
{
  const std::string &unit = args[1];
  unsigned int decimal_point = CRYPTONOTE_DISPLAY_DECIMAL_POINT;

  if (unit == "monero")
    decimal_point = CRYPTONOTE_DISPLAY_DECIMAL_POINT;
  else if (unit == "millinero")
    decimal_point = CRYPTONOTE_DISPLAY_DECIMAL_POINT - 3;
  else if (unit == "micronero")
    decimal_point = CRYPTONOTE_DISPLAY_DECIMAL_POINT - 6;
  else if (unit == "nanonero")
    decimal_point = CRYPTONOTE_DISPLAY_DECIMAL_POINT - 9;
  else if (unit == "piconero")
    decimal_point = 0;
  else
  {
    fail_msg_writer() << tr("单位无效");
    return true;
  }

  const auto pwd_container = get_and_verify_password();
  if (pwd_container)
  {
    cryptonote::set_default_decimal_point(decimal_point);
    m_wallet->rewrite(m_wallet_file, pwd_container->password());
  }
  return true;
}

bool simple_wallet::set_max_reorg_depth(const std::vector<std::string> &args/* = std::vector<std::string>()*/)
{
  uint64_t depth;
  if (!epee::string_tools::get_xtype_from_string(depth, args[1]))
  {
    fail_msg_writer() << tr("值无效");
    return true;
  }

  const auto pwd_container = get_and_verify_password();
  if (pwd_container)
  {
    m_wallet->max_reorg_depth(depth);
    m_wallet->rewrite(m_wallet_file, pwd_container->password());
  }
  return true;
}

bool simple_wallet::set_min_output_count(const std::vector<std::string> &args/* = std::vector<std::string>()*/)
{
  uint32_t count;
  if (!string_tools::get_xtype_from_string(count, args[1]))
  {
    fail_msg_writer() << tr("数量无效：必须是无符号整数");
    return true;
  }

  const auto pwd_container = get_and_verify_password();
  if (pwd_container)
  {
    m_wallet->set_min_output_count(count);
    m_wallet->rewrite(m_wallet_file, pwd_container->password());
  }
  return true;
}

bool simple_wallet::set_min_output_value(const std::vector<std::string> &args/* = std::vector<std::string>()*/)
{
  uint64_t value;
  if (!cryptonote::parse_amount(value, args[1]))
  {
    fail_msg_writer() << tr("值无效");
    return true;
  }

  const auto pwd_container = get_and_verify_password();
  if (pwd_container)
  {
    m_wallet->set_min_output_value(value);
    m_wallet->rewrite(m_wallet_file, pwd_container->password());
  }
  return true;
}

bool simple_wallet::set_merge_destinations(const std::vector<std::string> &args/* = std::vector<std::string>()*/)
{
  const auto pwd_container = get_and_verify_password();
  if (pwd_container)
  {
    parse_bool_and_use(args[1], [&](bool r) {
      m_wallet->merge_destinations(r);
      m_wallet->rewrite(m_wallet_file, pwd_container->password());
    });
  }
  return true;
}

bool simple_wallet::set_confirm_backlog(const std::vector<std::string> &args/* = std::vector<std::string>()*/)
{
  const auto pwd_container = get_and_verify_password();
  if (pwd_container)
  {
    parse_bool_and_use(args[1], [&](bool r) {
      m_wallet->confirm_backlog(r);
      m_wallet->rewrite(m_wallet_file, pwd_container->password());
    });
  }
  return true;
}

bool simple_wallet::set_confirm_backlog_threshold(const std::vector<std::string> &args/* = std::vector<std::string>()*/)
{
  uint32_t threshold;
  if (!string_tools::get_xtype_from_string(threshold, args[1]))
  {
    fail_msg_writer() << tr("数量无效：必须是无符号整数");
    return true;
  }

  const auto pwd_container = get_and_verify_password();
  if (pwd_container)
  {
    m_wallet->set_confirm_backlog_threshold(threshold);
    m_wallet->rewrite(m_wallet_file, pwd_container->password());
  }
  return true;
}

bool simple_wallet::set_confirm_export_overwrite(const std::vector<std::string> &args/* = std::vector<std::string>()*/)
{
  const auto pwd_container = get_and_verify_password();
  if (pwd_container)
  {
    parse_bool_and_use(args[1], [&](bool r) {
      m_wallet->confirm_export_overwrite(r);
      m_wallet->rewrite(m_wallet_file, pwd_container->password());
    });
  }
  return true;
}

bool simple_wallet::set_refresh_from_block_height(const std::vector<std::string> &args/* = std::vector<std::string>()*/)
{
  const auto pwd_container = get_and_verify_password();
  if (pwd_container)
  {
    uint64_t height;
    if (!epee::string_tools::get_xtype_from_string(height, args[1]))
    {
      fail_msg_writer() << tr("区块高度无效");
      return true;
    }
    m_wallet->set_refresh_from_block_height(height);
    m_wallet->rewrite(m_wallet_file, pwd_container->password());
  }
  return true;
}

bool simple_wallet::set_auto_low_priority(const std::vector<std::string> &args/* = std::vector<std::string>()*/)
{
  const auto pwd_container = get_and_verify_password();
  if (pwd_container)
  {
    parse_bool_and_use(args[1], [&](bool r) {
      m_wallet->auto_low_priority(r);
      m_wallet->rewrite(m_wallet_file, pwd_container->password());
    });
  }
  return true;
}

bool simple_wallet::set_segregate_pre_fork_outputs(const std::vector<std::string> &args/* = std::vector<std::string>()*/)
{
  const auto pwd_container = get_and_verify_password();
  if (pwd_container)
  {
    parse_bool_and_use(args[1], [&](bool r) {
      m_wallet->segregate_pre_fork_outputs(r);
      m_wallet->rewrite(m_wallet_file, pwd_container->password());
    });
  }
  return true;
}

bool simple_wallet::set_key_reuse_mitigation2(const std::vector<std::string> &args/* = std::vector<std::string>()*/)
{
  const auto pwd_container = get_and_verify_password();
  if (pwd_container)
  {
    parse_bool_and_use(args[1], [&](bool r) {
      m_wallet->key_reuse_mitigation2(r);
      m_wallet->rewrite(m_wallet_file, pwd_container->password());
    });
  }
  return true;
}

bool simple_wallet::set_subaddress_lookahead(const std::vector<std::string> &args/* = std::vector<std::string>()*/)
{
  const auto pwd_container = get_and_verify_password();
  if (pwd_container)
  {
    auto lookahead = parse_subaddress_lookahead(args[1]);
    if (lookahead)
    {
      m_wallet->set_subaddress_lookahead(lookahead->first, lookahead->second);
      m_wallet->rewrite(m_wallet_file, pwd_container->password());
    }
  }
  return true;
}

bool simple_wallet::set_segregation_height(const std::vector<std::string> &args/* = std::vector<std::string>()*/)
{
  const auto pwd_container = get_and_verify_password();
  if (pwd_container)
  {
    uint64_t height;
    if (!epee::string_tools::get_xtype_from_string(height, args[1]))
    {
      fail_msg_writer() << tr("区块高度无效");
      return true;
    }
    m_wallet->segregation_height(height);
    m_wallet->rewrite(m_wallet_file, pwd_container->password());
  }
  return true;
}

bool simple_wallet::set_ignore_fractional_outputs(const std::vector<std::string> &args/* = std::vector<std::string>()*/)
{
  const auto pwd_container = get_and_verify_password();
  if (pwd_container)
  {
    parse_bool_and_use(args[1], [&](bool r) {
      m_wallet->ignore_fractional_outputs(r);
      m_wallet->rewrite(m_wallet_file, pwd_container->password());
    });
  }
  return true;
}


bool simple_wallet::set_ignore_outputs_above(const std::vector<std::string> &args/* = std::vector<std::string>()*/)
{
  const auto pwd_container = get_and_verify_password();
  if (pwd_container)
  {
    uint64_t amount;
    if (!cryptonote::parse_amount(amount, args[1]))
    {
      fail_msg_writer() << tr("金额无效");
      return true;
    }
    if (amount == 0)
      amount = MONEY_SUPPLY;
    m_wallet->ignore_outputs_above(amount);
    m_wallet->rewrite(m_wallet_file, pwd_container->password());
  }
  return true;
}

bool simple_wallet::set_ignore_outputs_below(const std::vector<std::string> &args/* = std::vector<std::string>()*/)
{
  const auto pwd_container = get_and_verify_password();
  if (pwd_container)
  {
    uint64_t amount;
    if (!cryptonote::parse_amount(amount, args[1]))
    {
      fail_msg_writer() << tr("金额无效");
      return true;
    }
    m_wallet->ignore_outputs_below(amount);
    m_wallet->rewrite(m_wallet_file, pwd_container->password());
  }
  return true;
}

bool simple_wallet::set_track_uses(const std::vector<std::string> &args/* = std::vector<std::string>()*/)
{
  const auto pwd_container = get_and_verify_password();
  if (pwd_container)
  {
    parse_bool_and_use(args[1], [&](bool r) {
      m_wallet->track_uses(r);
      m_wallet->rewrite(m_wallet_file, pwd_container->password());
    });
  }
  return true;
}

bool simple_wallet::setup_background_sync(const std::vector<std::string> &args/* = std::vector<std::string>()*/)
{
  if (m_wallet->get_multisig_status().multisig_is_active)
  {
    fail_msg_writer() << tr("多重签名钱包尚未实现后台同步");
    return true;
  }
  if (m_wallet->watch_only())
  {
    fail_msg_writer() << tr("仅观察钱包尚未实现后台同步");
    return true;
  }
  if (m_wallet->key_on_device())
  {
    fail_msg_writer() << tr("硬件钱包不支持此命令");
    return true;
  }

  tools::wallet2::BackgroundSyncType background_sync_type;
  if (!parse_background_sync_type(args[1], background_sync_type))
  {
    fail_msg_writer() << tr("选项无效");
    return true;
  }

  const auto pwd_container = get_and_verify_password();
  if (!pwd_container)
    return true;

  try
  {
    boost::optional<epee::wipeable_string> background_cache_password = boost::none;
    if (background_sync_type == tools::wallet2::BackgroundSyncCustomPassword)
    {
      const auto background_pwd_container = background_sync_cache_password_prompter(true);
      if (!background_pwd_container)
        return true;
      background_cache_password = background_pwd_container->password();
    }

    LOCK_IDLE_SCOPE();
    m_wallet->setup_background_sync(background_sync_type, pwd_container->password(), background_cache_password);
  }
  catch (const std::exception &e)
  {
    fail_msg_writer() << tr("设置后台同步类型失败：") << e.what();
  }

  return true;
}

bool simple_wallet::set_show_wallet_name_when_locked(const std::vector<std::string> &args/* = std::vector<std::string>()*/)
{
  const auto pwd_container = get_and_verify_password();
  if (pwd_container)
  {
    parse_bool_and_use(args[1], [&](bool r) {
      m_wallet->show_wallet_name_when_locked(r);
      m_wallet->rewrite(m_wallet_file, pwd_container->password());
    });
  }
  return true;
}

bool simple_wallet::set_inactivity_lock_timeout(const std::vector<std::string> &args/* = std::vector<std::string>()*/)
{
#ifdef _WIN32
  tools::fail_msg_writer() << tr("Windows 上已禁用闲置锁定超时");
  return true;
#endif
  const auto pwd_container = get_and_verify_password();
  if (pwd_container)
  {
    uint32_t r;
    if (epee::string_tools::get_xtype_from_string(r, args[1]))
    {
      m_wallet->inactivity_lock_timeout(r);
      m_wallet->rewrite(m_wallet_file, pwd_container->password());
    }
    else
    {
      tools::fail_msg_writer() << tr("秒数无效");
    }
  }
  return true;
}

bool simple_wallet::set_setup_background_mining(const std::vector<std::string> &args/* = std::vector<std::string>()*/)
{
  const auto pwd_container = get_and_verify_password();
  if (pwd_container)
  {
    tools::wallet2::BackgroundMiningSetupType setup = tools::wallet2::BackgroundMiningMaybe;
    if (args[1] == "yes" || args[1] == "1")
      setup = tools::wallet2::BackgroundMiningYes;
    else if (args[1] == "no" || args[1] == "0")
      setup = tools::wallet2::BackgroundMiningNo;
    else
    {
      fail_msg_writer() << tr("参数无效：必须为 1/yes 或 0/no");
      return true;
    }
    m_wallet->setup_background_mining(setup);
    m_wallet->rewrite(m_wallet_file, pwd_container->password());
    if (setup == tools::wallet2::BackgroundMiningYes)
      start_background_mining();
    else
      stop_background_mining();
  }
  return true;
}

bool simple_wallet::set_device_name(const std::vector<std::string> &args/* = std::vector<std::string>()*/)
{
  const auto pwd_container = get_and_verify_password();
  if (pwd_container)
  {
    m_wallet->device_name(args[1]);
    bool r = false;
    try {
      r = m_wallet->reconnect_device();
      if (!r){
        fail_msg_writer() << tr("设备重新连接失败");
      }

    } catch(const std::exception & e){
      MWARNING("设备重新连接失败: " << e.what());
      fail_msg_writer() << tr("设备重新连接失败: ") << e.what();
    }

  }
  return true;
}

bool simple_wallet::set_export_format(const std::vector<std::string> &args/* = std::vector<std::string()*/)
{
  if (args.size() < 2)
  {
    fail_msg_writer() << tr("未指定导出格式");
    return true;
  }

  if (boost::algorithm::iequals(args[1], "ascii"))
  {
    m_wallet->set_export_format(tools::wallet2::ExportFormat::Ascii);
  }
  else if (boost::algorithm::iequals(args[1], "binary"))
  {
    m_wallet->set_export_format(tools::wallet2::ExportFormat::Binary);
  }
  else
  {
    fail_msg_writer() << tr("无法识别导出格式。");
    return true;
  }
  const auto pwd_container = get_and_verify_password();
  if (pwd_container)
  {
    m_wallet->rewrite(m_wallet_file, pwd_container->password());
  }
  return true;
}

bool simple_wallet::set_load_deprecated_formats(const std::vector<std::string> &args/* = std::vector<std::string()*/)
{
  if (args.size() < 2)
  {
    fail_msg_writer() << tr("未指定值");
    return true;
  }

  const auto pwd_container = get_and_verify_password();
  if (pwd_container)
  {
    parse_bool_and_use(args[1], [&](bool r) {
      if (r)
        fail_msg_writer() << tr("警告：deprecated formats use boost serialization, which has buffer overflows and crashes. Support for them has been discontinued.");
    });
  }
  return true;
}

bool simple_wallet::set_enable_multisig(const std::vector<std::string> &args/* = std::vector<std::string>()*/)
{
  if (args.size() < 2)
  {
    fail_msg_writer() << tr("未指定值");
    return true;
  }

  const auto pwd_container = get_and_verify_password();
  if (pwd_container)
  {
    parse_bool_and_use(args[1], [&](bool r) {
      m_wallet->enable_multisig(r);
      m_wallet->rewrite(m_wallet_file, pwd_container->password());
    });
  }
  return true;
}

bool simple_wallet::help(const std::vector<std::string> &args/* = std::vector<std::string>()*/)
{
  if(args.empty())
  {
    message_writer() << "";
    message_writer() << tr("重要命令：");
    message_writer() << "";
    message_writer() << tr("\"welcome\" - 显示欢迎信息。");
    message_writer() << tr("\"help all\" - 显示所有可用命令列表。");
    message_writer() << tr("\"help <command>\" - 显示指定命令的文档。");
    message_writer() << tr("\"apropos <keyword>\" - 显示与关键词相关的命令。");
    message_writer() << "";
    message_writer() << tr("\"wallet_info\" - 显示钱包主地址和其他信息。");
    message_writer() << tr("\"balance\" - 显示余额。");
    message_writer() << tr("\"address all\" - 显示所有地址。");
    message_writer() << tr("\"address new\" - 创建新的子地址。");
    message_writer() << tr("\"transfer <address> <amount>\" - 向指定地址发送 XMR。");
    message_writer() << tr("\"show_transfers [in|out|pending|failed|pool]\" - 显示交易。");
    message_writer() << tr("\"sweep_all <address>\" - 将全部余额发送到另一个钱包。");
    message_writer() << tr("“seed”——显示可用于恢复此钱包的 25 个秘密助记词。");
    message_writer() << tr("\"refresh\" - 将钱包与 Monero 网络同步。");
    message_writer() << tr("\"status\" - 查看钱包当前状态。");
    message_writer() << tr("\"version\" - 查看软件版本。");
    message_writer() << tr("\"exit\" - 退出钱包。");
    message_writer() << "";
    message_writer() << tr("\"donate <amount>\" - 向公共基金捐赠 XMR。");
    message_writer() << "";
  }
  else if ((args.size() == 1) && (args.front() == "all"))
  {
    success_msg_writer() << get_commands_str();
  }
  else if ((args.size() == 2) && (args.front() == "mms"))
  {
    // Little hack to be able to do "help mms <subcommand>"
    std::vector<std::string> mms_args(1, args.front() + " " + args.back());
    success_msg_writer() << get_command_usage(mms_args);
  }
  else
  {
    success_msg_writer() << get_command_usage(args);
  }
  return true;
}

bool simple_wallet::apropos(const std::vector<std::string> &args)
{
  if (args.empty())
  {
    PRINT_USAGE(USAGE_APROPOS);
    return true;
  }
  const std::vector<std::string>& command_list = m_cmd_binder.get_command_list(args);
  if (command_list.empty())
  {
    fail_msg_writer() << tr("没有找到与关键词相关的命令");
    return true;
  }

  success_msg_writer() << "";
  for(auto const& command:command_list)
  {
    std::vector<std::string> cmd;
    cmd.push_back(command);
    std::pair<std::string, std::string> documentation = m_cmd_binder.get_documentation(cmd);
    success_msg_writer() << "  " << documentation.first;
  }
  success_msg_writer() << "";

  return true;
}

bool simple_wallet::scan_tx(const std::vector<std::string> &args)
{
  CHECK_IF_BACKGROUND_SYNCING("cannot scan tx");
  if (args.empty())
  {
    PRINT_USAGE(USAGE_SCAN_TX);
    return true;
  }

  // Parse and dedup args
  std::unordered_set<crypto::hash> txids;
  for (const auto &s : args) {
    crypto::hash txid;
    if (!epee::string_tools::hex_to_pod(s, txid)) {
      fail_msg_writer() << tr("无效的交易 ID specified: ") << s;
      return true;
    }
    txids.insert(txid);
  }

  if (!m_wallet->is_trusted_daemon()) {
    message_writer(console_color_red, true) << tr("警告：此操作可能会将交易 ID 泄露给远程节点，并影响您的隐私");
    if (!command_line::is_yes(input_line("确定要继续吗？", true))) {
      message_writer() << tr("您已取消操作");
      return true;
    }
  }

  LOCK_IDLE_SCOPE();
  m_in_manual_refresh.store(true);
  try {
    m_wallet->scan_tx(txids);
  } catch (const tools::error::wont_reprocess_recent_txs_via_untrusted_daemon &e) {
    fail_msg_writer() << e.what() << ". Either connect to a 受信任 daemon by passing --trusted-daemon when starting the wallet, or use rescan_bc to rescan the chain.";
  } catch (const std::exception &e) {
    fail_msg_writer() << e.what();
  }
  m_in_manual_refresh.store(false);
  return true;
}

simple_wallet::simple_wallet()
  : m_refresh_progress_reporter(*this)
  , m_idle_run(true)
  , m_auto_refresh_enabled(false)
  , m_auto_refresh_refreshing(false)
  , m_in_manual_refresh(false)
  , m_current_subaddress_account(0)
  , m_last_activity_time(time(NULL))
  , m_locked(false)
  , m_in_command(false)
{
  m_cmd_binder.set_handler("start_mining",
                           boost::bind(&simple_wallet::on_command, this, &simple_wallet::start_mining, _1),
                           tr(USAGE_START_MINING),
                           tr("在守护进程中开始挖矿（bg_mining 和 ignore_battery 为可选布尔参数）。"));
  m_cmd_binder.set_handler("stop_mining",
                           boost::bind(&simple_wallet::on_command, this, &simple_wallet::stop_mining, _1),
                           tr("停止守护进程中的挖矿。"));
  m_cmd_binder.set_handler("set_daemon",
                           boost::bind(&simple_wallet::on_command, this, &simple_wallet::set_daemon, _1),
                           tr(USAGE_SET_DAEMON),
                           tr("设置要连接的其他守护进程。如果不是您自己的节点，它可能会监视您。"));
  m_cmd_binder.set_handler("save_bc",
                           boost::bind(&simple_wallet::on_command, this, &simple_wallet::save_bc, _1),
                           tr("保存当前区块链数据。"));
  m_cmd_binder.set_handler("refresh",
                           boost::bind(&simple_wallet::on_command, this, &simple_wallet::refresh, _1),
                           tr("同步交易和余额。"));
  m_cmd_binder.set_handler("balance",
                           boost::bind(&simple_wallet::on_command, this, &simple_wallet::show_balance, _1),
                           tr(USAGE_SHOW_BALANCE),
                           tr("显示当前选中账户的钱包余额。"));
  m_cmd_binder.set_handler("incoming_transfers",
                           boost::bind(&simple_wallet::on_command, this, &simple_wallet::show_incoming_transfers,_1),
                           tr(USAGE_INCOMING_TRANSFERS),
                           tr("Show the incoming transfers, all or filtered by availability and address index.\n\n"
                              "Output format:\n"
                              "Amount, Spent(\"T\"|\"F\"), \"frozen\"|\"locked\"|\"unlocked\", RingCT, Global Index, Transaction Hash, Address Index, [Public Key, Key Image] "));
  m_cmd_binder.set_handler("payments",
                           boost::bind(&simple_wallet::on_command, this, &simple_wallet::show_payments,_1),
                           tr(USAGE_PAYMENTS),
                           tr("显示指定支付 ID 的付款记录。"));
  m_cmd_binder.set_handler("bc_height",
                           boost::bind(&simple_wallet::on_command, this, &simple_wallet::show_blockchain_height, _1),
                           tr("显示区块链高度。"));
  m_cmd_binder.set_handler("transfer", boost::bind(&simple_wallet::on_command, this, &simple_wallet::transfer, _1),
                           tr(USAGE_TRANSFER),
                           tr("transfer <address> <amount>。指定 \"index=<N1>[,<N2>,...]\" 参数时，钱包只使用这些地址索引收到的输出；未指定时，钱包会随机选择地址索引。钱包会尽量避免合并多个地址的输出。<priority> 是交易优先级，优先级越高，手续费越高。优先级从低到高依次为：unimportant、normal、elevated、priority；未指定时使用默认值（参见 \"set priority\"）。<ring_size> 是用于增加不可追踪性的输入数量。可以在付款 ID（如果提供）之前增加 URI_2 或 <address_2> <amount_2> 等参数来同时完成多笔付款。\"subtractfeefrom=\" 列表用于指定从哪些收款目标扣除交易手续费，而不是从找零中扣除。手续费会按比例均摊到所选目标。例如，若对三个目标转账并从第一个和第三个目标扣费，可使用：\"transfer <addr1> 3 <addr2> 0.5 <addr3> 1 subtractfeefrom=0,2\"。假设手续费为 0.1，则余额（含手续费）正好减少 4.5 XMR，addr1 和 addr3 分别收到 2.925 和 0.975 XMR。使用 \"subtractfeefrom=all\" 可将手续费分摊到所有目标。"));
  m_cmd_binder.set_handler("sweep_unmixable",
                           boost::bind(&simple_wallet::on_command, this, &simple_wallet::sweep_unmixable, _1),
                           tr("使用 ring_size 1 将所有无法混淆的输出发送给自己"));
  m_cmd_binder.set_handler("sweep_all", boost::bind(&simple_wallet::on_command, this, &simple_wallet::sweep_all, _1),
                           tr(USAGE_SWEEP_ALL),
                           tr("将全部可用余额发送到指定地址。如果指定 \"index=<N1>[,<N2>,...]\" 或 \"index=all\"，钱包分别清扫这些地址索引或所有地址索引收到的输出。未指定时，钱包会随机选择地址索引。如果指定 \"outputs=<N>\" 且 N > 0，钱包会将交易平均拆分为 N 个输出。"));
  m_cmd_binder.set_handler("sweep_account", boost::bind(&simple_wallet::on_command, this, &simple_wallet::sweep_account, _1),
                           tr(USAGE_SWEEP_ACCOUNT),
                           tr("将指定账户的全部可用余额发送到指定地址。如果指定 \"index=<N1>[,<N2>,...]\" 或 \"index=all\"，钱包分别清扫这些地址索引或所有地址索引收到的输出。未指定时，钱包会随机选择地址索引。如果指定 \"outputs=<N>\" 且 N > 0，钱包会将交易平均拆分为 N 个输出。"));
  m_cmd_binder.set_handler("sweep_below",
                           boost::bind(&simple_wallet::on_command, this, &simple_wallet::sweep_below, _1),
                           tr(USAGE_SWEEP_BELOW),
                           tr("将低于指定阈值的全部可用输出发送到指定地址。"));
  m_cmd_binder.set_handler("sweep_single",
                           boost::bind(&simple_wallet::on_command, this, &simple_wallet::sweep_single, _1),
                           tr(USAGE_SWEEP_SINGLE),
                           tr("将指定密钥镜像对应的单个输出发送到指定地址，不产生找零。"));
  m_cmd_binder.set_handler("donate",
                           boost::bind(&simple_wallet::on_command, this, &simple_wallet::donate, _1),
                           tr(USAGE_DONATE),
                           tr("向公共基金捐赠 <amount>（donate.getmonero.org）。"));
  m_cmd_binder.set_handler("sign_transfer",
                           boost::bind(&simple_wallet::on_command, this, &simple_wallet::sign_transfer, _1),
                           tr(USAGE_SIGN_TRANSFER),
                           tr("Sign a transaction from a file. If the parameter \"export_raw\" is specified, transaction raw hex data suitable for the daemon RPC /sendrawtransaction is exported.\n"
                              "Use the parameter <filename> to specify the file to read from. If not specified, the default \"unsigned_monero_tx\" will be used."));
  m_cmd_binder.set_handler("submit_transfer",
                           boost::bind(&simple_wallet::on_command, this, &simple_wallet::submit_transfer, _1),
                           tr("从文件提交已签名的交易。"));
  m_cmd_binder.set_handler("set_log",
                           boost::bind(&simple_wallet::on_command, this, &simple_wallet::set_log, _1),
                           tr(USAGE_SET_LOG),
                           tr("更改当前日志详细程度（级别必须为 <0-4>）。"));
  m_cmd_binder.set_handler("account",
                           boost::bind(&simple_wallet::on_command, this, &simple_wallet::account, _1),
                           tr(USAGE_ACCOUNT),
                           tr("If no arguments are specified, the wallet shows all the existing accounts along with their balances.\n"
                              "If the \"new\" argument is specified, the wallet creates a new account with its label initialized by the provided label text (which can be empty).\n"
                              "If the \"switch\" argument is specified, the wallet switches to the account specified by <index>.\n"
                              "If the \"label\" argument is specified, the wallet sets the label of the account specified by <index> to the provided label text.\n"
                              "If the \"tag\" argument is specified, a tag <tag_name> is assigned to the specified accounts <account_index_1>, <account_index_2>, ....\n"
                              "If the \"untag\" argument is specified, the tags assigned to the specified accounts <account_index_1>, <account_index_2> ..., are removed.\n"
                              "If the \"tag_description\" argument is specified, the tag <tag_name> is assigned an arbitrary text <description>."));
  m_cmd_binder.set_handler("address",
                           boost::bind(&simple_wallet::on_command, this, &simple_wallet::print_address, _1),
                           tr(USAGE_ADDRESS),
                           tr("If no arguments are specified or <index> is specified, the wallet shows the default or specified address. If \"all\" is specified, the wallet shows all the existing addresses in the currently selected account. If \"new \" is specified, the wallet creates a new address with the provided label text (which can be empty). If \"mnew\" is specified, the wallet creates as many new addresses as specified by the argument; the default label is set for the new addresses. If \"label\" is specified, the wallet sets the label of the address specified by <index> to the provided label text. If \"one-off\" is specified, the address for the specified index is generated and displayed, and remembered by the wallet"));
  m_cmd_binder.set_handler("integrated_address",
                           boost::bind(&simple_wallet::on_command, this, &simple_wallet::print_integrated_address, _1),
                           tr(USAGE_INTEGRATED_ADDRESS),
                           tr("将付款 ID 编码到当前钱包公钥地址对应的集成地址中（不提供参数时使用随机付款 ID），或将集成地址解码为标准地址和付款 ID。"));
  m_cmd_binder.set_handler("address_book",
                           boost::bind(&simple_wallet::on_command, this, &simple_wallet::address_book,_1),
                           tr(USAGE_ADDRESS_BOOK),
                           tr("显示地址簿中的所有条目，也可以添加或删除地址簿条目。"));
  m_cmd_binder.set_handler("save",
                           boost::bind(&simple_wallet::on_command, this, &simple_wallet::save, _1),
                           tr("保存钱包数据。"));
  m_cmd_binder.set_handler("save_watch_only",
                           boost::bind(&simple_wallet::on_command, this, &simple_wallet::save_watch_only, _1),
                           tr("保存仅观察钱包密钥文件。"));
  m_cmd_binder.set_handler("viewkey",
                           boost::bind(&simple_wallet::on_command, this, &simple_wallet::viewkey, _1),
                           tr("显示私有查看密钥。"));
  m_cmd_binder.set_handler("spendkey",
                           boost::bind(&simple_wallet::on_command, this, &simple_wallet::spendkey, _1),
                           tr("显示私有支出密钥。"));
  m_cmd_binder.set_handler("seed",
                           boost::bind(&simple_wallet::on_command, this, &simple_wallet::seed, _1),
                           tr("显示 Electrum 风格助记词"));
  m_cmd_binder.set_handler("legacy_seed",
                           boost::bind(&simple_wallet::on_command, this, &simple_wallet::legacy_seed, _1),
                           tr("将 Polyseed 显示为传统助记词"));
  m_cmd_binder.set_handler("restore_height",
                           boost::bind(&simple_wallet::on_command, this, &simple_wallet::restore_height, _1),
                           tr("显示恢复高度"));
  m_cmd_binder.set_handler("set",
                           boost::bind(&simple_wallet::on_command, this, &simple_wallet::set_variable, _1),
                           tr(USAGE_SET_VARIABLE),
                           tr("Available options:\n "
                                  "seed language\n "
                                  "  Set the wallet's seed language.\n "
                                  "always-confirm-transfers <1|0>\n "
                                  "  Whether to confirm unsplit txes.\n "
                                  "print-ring-members <1|0>\n "
                                  "  Whether to print detailed information about ring members during confirmation.\n "
                                  "store-tx-info <1|0>\n "
                                  "  Whether to store outgoing tx info (destination address, payment ID, tx secret key) for future reference.\n "
                                  "auto-refresh <1|0>\n "
                                  "  Whether to automatically synchronize new blocks from the daemon.\n "
                                  "refresh-type <full|optimize-coinbase|no-coinbase|default>\n "
                                  "  Set the wallet's refresh behaviour.\n "
                                  "priority [0|1|2|3|4]\n "
                                  "  Set the fee to default/unimportant/normal/elevated/priority.\n "
                                  "confirm-missing-payment-id <1|0> (obsolete)\n "
                                  "ask-password <0|1|2   (or never|action|decrypt)>\n "
                                  "  action: ask the password before many actions such as transfer, etc\n "
                                  "  decrypt: same as action, but keeps the spend key encrypted in memory when not needed\n "
                                  "unit <monero|millinero|micronero|nanonero|piconero>\n "
                                  "  Set the default monero (sub-)unit.\n "
                                  "max-reorg-depth <unsigned int>\n "
                                  "  Set the maximum amount of blocks to accept in a reorg.\n "
                                  "min-outputs-count [n]\n "
                                  "  Try to keep at least that many outputs of value at least min-outputs-value.\n "
                                  "min-outputs-value [n]\n "
                                  "  Try to keep at least min-outputs-count outputs of at least that value.\n "
                                  "merge-destinations <1|0>\n "
                                  "  Whether to merge multiple payments to the same destination address.\n "
                                  "confirm-backlog <1|0>\n "
                                  "  Whether to warn if there is transaction backlog.\n "
                                  "confirm-backlog-threshold [n]\n "
                                  "  Set a threshold for confirm-backlog to only warn if the transaction backlog is greater than n blocks.\n "
                                  "confirm-export-overwrite <1|0>\n "
                                  "  Whether to warn if the file to be exported already exists.\n "
                                  "refresh-from-block-height [n]\n "
                                  "  Set the height before which to ignore blocks.\n "
                                  "auto-low-priority <1|0>\n "
                                  "  Whether to automatically use the low priority fee level when it's safe to do so.\n "
                                  "segregate-pre-fork-outputs <1|0>\n "
                                  "  Set this if you intend to spend outputs on both Monero AND a key reusing fork.\n "
                                  "key-reuse-mitigation2 <1|0>\n "
                                  "  Set this if you are not sure whether you will spend on a key reusing Monero fork later.\n "
                                  "subaddress-lookahead <major>:<minor>\n "
                                  "  Set the lookahead sizes for the subaddress hash table.\n "
                                  "segregation-height <n>\n "
                                  "  Set to the height of a key reusing fork you want to use, 0 to use default.\n "
                                  "ignore-fractional-outputs <1|0>\n "
                                  "  Whether to ignore fractional outputs that result in net loss when spending due to fee.\n "
                                  "ignore-outputs-above <amount>\n "
                                  "  Ignore outputs of amount above this threshold when spending. Value 0 is translated to the maximum value (18 million) which disables this filter.\n "
                                  "ignore-outputs-below <amount>\n "
                                  "  Ignore outputs of amount below this threshold when spending.\n "
                                  "track-uses <1|0>\n "
                                  "  Whether to keep track of owned outputs uses.\n "
                                  "background-sync <off|reuse-wallet-password|custom-background-password>\n "
                                  "  Set this to enable scanning in the background with just the view key while the wallet is locked.\n "
                                  "setup-background-mining <1|0>\n "
                                  "  Whether to enable background mining. Set this to support the network and to get a chance to receive new monero.\n "
                                  "device-name <device_name[:device_spec]>\n "
                                  "  Device name for hardware wallet.\n "
                                  "export-format <\"binary\"|\"ascii\">\n "
                                  "  Save all exported files as binary (cannot be copied and pasted) or ascii (can be).\n "
                                  "load-deprecated-formats <1|0>\n "
                                  "  Whether to enable importing data in deprecated formats.\n "
                                  "show-wallet-name-when-locked <1|0>\n "
                                  "  Set this if you would like to display the wallet name when locked.\n "
                                  "enable-multisig-experimental <1|0>\n "
                                  "  Set this to allow multisig commands. 多重签名 may currently be exploitable if parties do not trust each other.\n "
                                  "inactivity-lock-timeout <unsigned int>\n "
                                  "  How many seconds to wait before locking the wallet (0 to disable)."));
  m_cmd_binder.set_handler("encrypted_seed",
                           boost::bind(&simple_wallet::on_command, this, &simple_wallet::encrypted_seed, _1),
                           tr("显示已加密的 Electrum 风格助记词。"));
  m_cmd_binder.set_handler("rescan_spent",
                           boost::bind(&simple_wallet::on_command, this, &simple_wallet::rescan_spent, _1),
                           tr("重新扫描区块链中的已花费输出。"));
  m_cmd_binder.set_handler("get_tx_key",
                           boost::bind(&simple_wallet::on_command, this, &simple_wallet::get_tx_key, _1),
                           tr(USAGE_GET_TX_KEY),
                           tr("获取指定 <txid> 的交易密钥（r）。"));
  m_cmd_binder.set_handler("set_tx_key",
                           boost::bind(&simple_wallet::on_command, this, &simple_wallet::set_tx_key, _1),
                           tr(USAGE_SET_TX_KEY),
                           tr("设置指定 <txid> 的交易密钥（r），用于交易由其他设备或第三方钱包创建的情况。"));
  m_cmd_binder.set_handler("check_tx_key",
                           boost::bind(&simple_wallet::on_command, this, &simple_wallet::check_tx_key, _1),
                           tr(USAGE_CHECK_TX_KEY),
                           tr("检查 <txid> 中发送到 <address> 的金额。"));
  m_cmd_binder.set_handler("get_tx_proof",
                           boost::bind(&simple_wallet::on_command, this, &simple_wallet::get_tx_proof, _1),
                           tr(USAGE_GET_TX_PROOF),
                           tr("生成证明 <txid> 中资金已发送到 <address> 的签名，可选提供挑战字符串 <message>。当 <address> 不是您的钱包地址时使用交易私钥，否则使用查看私钥；此过程不会泄露私钥。"));
  m_cmd_binder.set_handler("check_tx_proof",
                           boost::bind(&simple_wallet::on_command, this, &simple_wallet::check_tx_proof, _1),
                           tr(USAGE_CHECK_TX_PROOF),
                           tr("检查 <txid> 中发送到 <address> 的资金证明；如提供 <message>，同时检查挑战字符串。"));
  m_cmd_binder.set_handler("get_spend_proof",
                           boost::bind(&simple_wallet::on_command, this, &simple_wallet::get_spend_proof, _1),
                           tr(USAGE_GET_SPEND_PROOF),
                           tr("使用支出私钥生成证明您创建了 <txid> 的签名，可选提供挑战字符串 <message>。"));
  m_cmd_binder.set_handler("check_spend_proof",
                           boost::bind(&simple_wallet::on_command, this, &simple_wallet::check_spend_proof, _1),
                           tr(USAGE_CHECK_SPEND_PROOF),
                           tr("检查证明签名者创建了 <txid> 的签名，可选提供挑战字符串 <message>。"));
  m_cmd_binder.set_handler("get_reserve_proof",
                           boost::bind(&simple_wallet::on_command, this, &simple_wallet::get_reserve_proof, _1),
                           tr(USAGE_GET_RESERVE_PROOF),
                           tr("Generate a signature proving that you own at least this much, optionally with a challenge string <message>.\n"
                              "If 'all' is specified, you prove the entire sum of all of your existing accounts' balances.\n"
                              "Otherwise, you prove the reserve of the smallest possible amount above <amount> available in your current account."));
  m_cmd_binder.set_handler("check_reserve_proof",
                           boost::bind(&simple_wallet::on_command, this, &simple_wallet::check_reserve_proof, _1),
                           tr(USAGE_CHECK_RESERVE_PROOF),
                           tr("检查证明 <address> 所有者至少持有指定金额的签名，可选提供挑战字符串 <message>。"));
  m_cmd_binder.set_handler("show_transfers",
                           boost::bind(&simple_wallet::on_command, this, &simple_wallet::show_transfers, _1),
                           tr(USAGE_SHOW_TRANSFERS),
                           // Seemingly broken formatting to compensate for the backslash before the quotes.
                           tr("Show the incoming/outgoing transfers within an optional height range.\n\n"
                              "Output format:\n"
                              "In or Coinbase:    Block Number, \"block\"|\"in\",              Time, Amount,  Transaction Hash, Payment ID, Subaddress Index,                     \"-\", Note\n"
                              "Out:               Block Number, \"out\",                     Time, Amount*, Transaction Hash, Payment ID, Fee, Destinations, Input addresses**, \"-\", Note\n"
                              "Pool:                            \"pool\", \"in\",              Time, Amount,  Transaction Hash, Payment Id, Subaddress Index,                     \"-\", Note, Double Spend Note\n"
                              "Pending or Failed:               \"failed\"|\"pending\", \"out\", Time, Amount*, Transaction Hash, Payment ID, Fee, Input addresses**,               \"-\", Note\n\n"
                              "* Excluding change and fee.\n"
                              "** Set of address indices used as inputs in this transfer."));
  m_cmd_binder.set_handler("export_transfers",
                           boost::bind(&simple_wallet::on_command, this, &simple_wallet::export_transfers, _1),
                           tr("export_transfers [in|out|all|pending|failed|pool|coinbase] [index=<N1>[,<N2>,...]] [<min_height> [<max_height>]] [output=<filepath>] [option=<with_keys>]"),
                           tr("将指定区块高度范围内的入账/出账转账导出为 CSV。"));
  m_cmd_binder.set_handler("unspent_outputs",
                           boost::bind(&simple_wallet::on_command, this, &simple_wallet::unspent_outputs, _1),
                           tr(USAGE_UNSPENT_OUTPUTS),
                           tr("显示指定地址在可选金额范围内的未花费输出。"));
  m_cmd_binder.set_handler("rescan_bc",
                           boost::bind(&simple_wallet::on_command, this, &simple_wallet::rescan_blockchain, _1),
                           tr(USAGE_RESCAN_BC),
                           tr("从头重新扫描区块链。指定 \"hard\" 时，会丢失无法仅从区块链本身恢复的信息。"));
  m_cmd_binder.set_handler("set_tx_note",
                           boost::bind(&simple_wallet::on_command, this, &simple_wallet::set_tx_note, _1),
                           tr(USAGE_SET_TX_NOTE),
                           tr("为 <txid> 设置任意字符串备注。"));
  m_cmd_binder.set_handler("get_tx_note",
                           boost::bind(&simple_wallet::on_command, this, &simple_wallet::get_tx_note, _1),
                           tr(USAGE_GET_TX_NOTE),
                           tr("获取交易的字符串备注。"));
  m_cmd_binder.set_handler("set_description",
                           boost::bind(&simple_wallet::on_command, this, &simple_wallet::set_description, _1),
                           tr(USAGE_SET_DESCRIPTION),
                           tr("为钱包设置任意描述。"));
  m_cmd_binder.set_handler("get_description",
                           boost::bind(&simple_wallet::on_command, this, &simple_wallet::get_description, _1),
                           tr(USAGE_GET_DESCRIPTION),
                           tr("获取钱包描述。"));
  m_cmd_binder.set_handler("status",
                           boost::bind(&simple_wallet::on_command, this, &simple_wallet::status, _1),
                           tr("显示钱包状态。"));
  m_cmd_binder.set_handler("wallet_info",
                           boost::bind(&simple_wallet::on_command, this, &simple_wallet::wallet_info, _1),
                           tr("显示钱包信息。"));
  m_cmd_binder.set_handler("sign",
                           boost::bind(&simple_wallet::on_command, this, &simple_wallet::sign, _1),
                           tr(USAGE_SIGN),
                           tr("使用指定子地址（未指定时使用主地址）对文件内容进行签名。"));
  m_cmd_binder.set_handler("verify",
                           boost::bind(&simple_wallet::on_command, this, &simple_wallet::verify, _1),
                           tr(USAGE_VERIFY),
                           tr("验证文件内容的签名。"));
  m_cmd_binder.set_handler("export_key_images",
                           boost::bind(&simple_wallet::on_command, this, &simple_wallet::export_key_images, _1),
                           tr(USAGE_EXPORT_KEY_IMAGES),
                           tr("将已签名的密钥镜像列表导出到 <filename>。"));
  m_cmd_binder.set_handler("import_key_images",
                           boost::bind(&simple_wallet::on_command, this, &simple_wallet::import_key_images, _1),
                           tr(USAGE_IMPORT_KEY_IMAGES),
                           tr("导入已签名的密钥镜像列表并验证其花费状态。"));
  m_cmd_binder.set_handler("hw_key_images_sync",
                           boost::bind(&simple_wallet::on_command, this, &simple_wallet::hw_key_images_sync, _1),
                           tr(USAGE_HW_KEY_IMAGES_SYNC),
                           tr("将密钥镜像与硬件钱包同步。"));
  m_cmd_binder.set_handler("hw_reconnect",
                           boost::bind(&simple_wallet::on_command, this, &simple_wallet::hw_reconnect, _1),
                           tr(USAGE_HW_RECONNECT),
                           tr("尝试重新连接硬件钱包。"));
  m_cmd_binder.set_handler("export_outputs",
                           boost::bind(&simple_wallet::on_command, this, &simple_wallet::export_outputs, _1),
                           tr(USAGE_EXPORT_OUTPUTS),
                           tr("导出此钱包拥有的一组输出。"));
  m_cmd_binder.set_handler("import_outputs",
                           boost::bind(&simple_wallet::on_command, this, &simple_wallet::import_outputs, _1),
                           tr(USAGE_IMPORT_OUTPUTS),
                           tr("导入此钱包拥有的一组输出。"));
  m_cmd_binder.set_handler("show_transfer",
                           boost::bind(&simple_wallet::on_command, this, &simple_wallet::show_transfer, _1),
                           tr(USAGE_SHOW_TRANSFER),
                           tr("显示与此地址相关的转账信息。"));
  m_cmd_binder.set_handler("password",
                           boost::bind(&simple_wallet::on_command, this, &simple_wallet::change_password, _1),
                           tr("修改钱包密码。"));
  m_cmd_binder.set_handler("payment_id",
                           boost::bind(&simple_wallet::on_command, this, &simple_wallet::payment_id, _1),
                           tr(USAGE_PAYMENT_ID),
                           tr("生成新的随机完整长度付款 ID（已废弃）。此类付款 ID 在区块链上不加密；加密的短付款 ID 请使用 integrated_address。"));
  m_cmd_binder.set_handler("fee",
                           boost::bind(&simple_wallet::on_command, this, &simple_wallet::print_fee_info, _1),
                           tr("显示当前手续费和交易积压信息。"));
  m_cmd_binder.set_handler("prepare_multisig", boost::bind(&simple_wallet::on_command, this, &simple_wallet::prepare_multisig, _1),
                           tr("导出创建多重签名钱包所需的数据"));
  m_cmd_binder.set_handler("make_multisig", boost::bind(&simple_wallet::on_command, this, &simple_wallet::make_multisig, _1),
                           tr(USAGE_MAKE_MULTISIG),
                           tr("将此钱包转换为多重签名钱包"));
  m_cmd_binder.set_handler("exchange_multisig_keys",
                           boost::bind(&simple_wallet::on_command, this, &simple_wallet::exchange_multisig_keys, _1),
                           tr(USAGE_EXCHANGE_MULTISIG_KEYS),
                           tr("执行额外的多重签名密钥交换轮次，用于任意 M/N 多重签名钱包"));
  m_cmd_binder.set_handler("export_multisig_info",
                           boost::bind(&simple_wallet::on_command, this, &simple_wallet::export_multisig, _1),
                           tr(USAGE_EXPORT_MULTISIG_INFO),
                           tr("导出供其他参与者使用的多重签名信息"));
  m_cmd_binder.set_handler("import_multisig_info",
                           boost::bind(&simple_wallet::on_command, this, &simple_wallet::import_multisig, _1),
                           tr(USAGE_IMPORT_MULTISIG_INFO),
                           tr("导入其他参与者的多重签名信息"));
  m_cmd_binder.set_handler("sign_multisig",
                           boost::bind(&simple_wallet::on_command, this, &simple_wallet::sign_multisig, _1),
                           tr(USAGE_SIGN_MULTISIG),
                           tr("从文件签署多重签名交易"));
  m_cmd_binder.set_handler("submit_multisig",
                           boost::bind(&simple_wallet::on_command, this, &simple_wallet::submit_multisig, _1),
                           tr(USAGE_SUBMIT_MULTISIG),
                           tr("提交文件中的已签名多重签名交易"));
  m_cmd_binder.set_handler("export_raw_multisig_tx",
                           boost::bind(&simple_wallet::on_command, this, &simple_wallet::export_raw_multisig, _1),
                           tr(USAGE_EXPORT_RAW_MULTISIG_TX),
                           tr("将已签名的多重签名交易导出到文件"));
  m_cmd_binder.set_handler("mms",
                           boost::bind(&simple_wallet::on_command, this, &simple_wallet::mms, _1),
                           tr(USAGE_MMS),
                           tr("Interface with the MMS (多重签名 Messaging System)\n"
                              "<subcommand> is one of:\n"
                              "  init, info, signer, list, next, sync, transfer, delete, send, receive, export, note, show, set, help\n"
                              "  send_signer_config, start_auto_config, stop_auto_config, auto_config, config_checksum\n"
                              "Get help about a subcommand with: help mms <subcommand>, or help mms <subcommand>"));
  m_cmd_binder.set_handler("mms init",
                           boost::bind(&simple_wallet::on_command, this, &simple_wallet::mms, _1),
                           tr(USAGE_MMS_INIT),
                           tr("初始化并配置 M/N 多重签名 MMS，其中 M 为所需签名者数量，N 为授权签名者数量。"));
  m_cmd_binder.set_handler("mms info",
                           boost::bind(&simple_wallet::on_command, this, &simple_wallet::mms, _1),
                           tr(USAGE_MMS_INFO),
                           tr("显示当前 MMS 配置"));
  m_cmd_binder.set_handler("mms signer",
                           boost::bind(&simple_wallet::on_command, this, &simple_wallet::mms, _1),
                           tr(USAGE_MMS_SIGNER),
                           tr("设置或修改授权签名者信息（单词标签、传输地址、Monero 地址），或列出所有签名者。"));
  m_cmd_binder.set_handler("mms list",
                           boost::bind(&simple_wallet::on_command, this, &simple_wallet::mms, _1),
                           tr(USAGE_MMS_LIST),
                           tr("列出所有消息"));
  m_cmd_binder.set_handler("mms next",
                           boost::bind(&simple_wallet::on_command, this, &simple_wallet::mms, _1),
                           tr(USAGE_MMS_NEXT),
                           tr("Evaluate the next possible multisig-related action(s) according to wallet state, and execute or offer for choice\n"
                              "By using 'sync' processing of waiting messages with multisig sync info can be forced regardless of wallet state"));
  m_cmd_binder.set_handler("mms sync",
                           boost::bind(&simple_wallet::on_command, this, &simple_wallet::mms, _1),
                           tr(USAGE_MMS_SYNC),
                           tr("无论钱包状态如何都强制生成多重签名同步信息，用于从 \"stale data\" 等特殊错误中恢复。"));
  m_cmd_binder.set_handler("mms transfer",
                           boost::bind(&simple_wallet::on_command, this, &simple_wallet::mms, _1),
                           tr(USAGE_MMS_TRANSFER),
                           tr("发起支持 MMS 的转账；参数与普通 transfer 命令相同，具体说明请参见 transfer。"));
  m_cmd_binder.set_handler("mms delete",
                           boost::bind(&simple_wallet::on_command, this, &simple_wallet::mms, _1),
                           tr(USAGE_MMS_DELETE),
                           tr("提供消息 ID 删除单条消息，或使用 'all' 删除所有消息"));
  m_cmd_binder.set_handler("mms send",
                           boost::bind(&simple_wallet::on_command, this, &simple_wallet::mms, _1),
                           tr(USAGE_MMS_SEND),
                           tr("提供消息 ID 发送单条消息，或发送所有等待中的消息"));
  m_cmd_binder.set_handler("mms receive",
                           boost::bind(&simple_wallet::on_command, this, &simple_wallet::mms, _1),
                           tr(USAGE_MMS_RECEIVE),
                           tr("立即检查是否有新消息可接收"));
  m_cmd_binder.set_handler("mms export",
                           boost::bind(&simple_wallet::on_command, this, &simple_wallet::mms, _1),
                           tr(USAGE_MMS_EXPORT),
                           tr("将消息内容写入文件 \"mms_message_content\"。"));
  m_cmd_binder.set_handler("mms note",
                           boost::bind(&simple_wallet::on_command, this, &simple_wallet::mms, _1),
                           tr(USAGE_MMS_NOTE),
                           tr("Send a one-line message to an authorized signer, identified by its label, or show any waiting unread notes"));
  m_cmd_binder.set_handler("mms show",
                           boost::bind(&simple_wallet::on_command, this, &simple_wallet::mms, _1),
                           tr(USAGE_MMS_SHOW),
                           tr("显示单条消息的详细信息"));
  m_cmd_binder.set_handler("mms set",
                           boost::bind(&simple_wallet::on_command, this, &simple_wallet::mms, _1),
                           tr(USAGE_MMS_SET),
                           tr("Available options:\n "
                                  "auto-send <1|0>\n "
                                  "  Whether to automatically send newly generated messages right away.\n "));
  m_cmd_binder.set_handler("mms send_signer_config",
                           boost::bind(&simple_wallet::on_command, this, &simple_wallet::mms, _1),
                           tr(USAGE_MMS_SEND_SIGNER_CONFIG),
                           tr("将完成的签名者配置发送给所有其他授权签名者"));
  m_cmd_binder.set_handler("mms start_auto_config",
                           boost::bind(&simple_wallet::on_command, this, &simple_wallet::mms, _1),
                           tr(USAGE_MMS_START_AUTO_CONFIG),
                           tr("Start auto-config at the auto-config manager's wallet by issuing auto-config tokens and optionally set others' labels"));
  m_cmd_binder.set_handler("mms config_checksum",
                           boost::bind(&simple_wallet::on_command, this, &simple_wallet::mms, _1),
                           tr(USAGE_MMS_CONFIG_CHECKSUM),
                           tr("获取校验和，以便签名者快速检查 MMS 配置是否一致"));
  m_cmd_binder.set_handler("mms stop_auto_config",
                           boost::bind(&simple_wallet::on_command, this, &simple_wallet::mms, _1),
                           tr(USAGE_MMS_STOP_AUTO_CONFIG),
                           tr("Delete any auto-config tokens and abort a auto-config process"));
  m_cmd_binder.set_handler("mms auto_config",
                           boost::bind(&simple_wallet::on_command, this, &simple_wallet::mms, _1),
                           tr(USAGE_MMS_AUTO_CONFIG),
                           tr("Start auto-config by using the token received from the auto-config manager"));
  m_cmd_binder.set_handler("print_ring",
                           boost::bind(&simple_wallet::on_command, this, &simple_wallet::print_ring, _1),
                           tr(USAGE_PRINT_RING),
                           tr("Print the ring(s) used to spend a given key image or transaction (if the ring size is > 1)\n\n"
                              "Output format:\n"
                              "Key Image, \"absolute\", list of rings"));
  m_cmd_binder.set_handler("set_ring",
                           boost::bind(&simple_wallet::on_command, this, &simple_wallet::set_ring, _1),
                           tr(USAGE_SET_RING),
                           tr("Set the ring used for a given key image, so it can be reused in a fork"));
  m_cmd_binder.set_handler("unset_ring",
                           boost::bind(&simple_wallet::on_command, this, &simple_wallet::unset_ring, _1),
                           tr(USAGE_UNSET_RING),
                           tr("Unsets the ring used for a given key image or transaction"));
  m_cmd_binder.set_handler("save_known_rings",
                           boost::bind(&simple_wallet::on_command, this, &simple_wallet::save_known_rings, _1),
                           tr(USAGE_SAVE_KNOWN_RINGS),
                           tr("Save known rings to the shared rings database"));
  m_cmd_binder.set_handler("freeze",
                           boost::bind(&simple_wallet::on_command, this, &simple_wallet::freeze, _1),
                           tr(USAGE_FREEZE),
                           tr("Freeze a single output by key image so it will not be used"));
  m_cmd_binder.set_handler("thaw",
                           boost::bind(&simple_wallet::on_command, this, &simple_wallet::thaw, _1),
                           tr(USAGE_THAW),
                           tr("Thaw a single output by key image so it may be used again"));
  m_cmd_binder.set_handler("frozen",
                           boost::bind(&simple_wallet::on_command, this, &simple_wallet::frozen, _1),
                           tr(USAGE_FROZEN),
                           tr("Checks whether a given output is currently frozen by key image"));
  m_cmd_binder.set_handler("lock",
                           boost::bind(&simple_wallet::on_command, this, &simple_wallet::lock, _1),
                           tr(USAGE_LOCK),
                           tr("锁定钱包控制台，继续操作需要输入钱包密码"));
  m_cmd_binder.set_handler("net_stats",
                           boost::bind(&simple_wallet::on_command, this, &simple_wallet::net_stats, _1),
                           tr(USAGE_NET_STATS),
                           tr("显示基本网络统计信息"));
  m_cmd_binder.set_handler("public_nodes",
                           boost::bind(&simple_wallet::on_command, this, &simple_wallet::public_nodes, _1),
                           tr(USAGE_PUBLIC_NODES),
                           tr("列出已知公共节点"));
  m_cmd_binder.set_handler("welcome",
                           boost::bind(&simple_wallet::on_command, this, &simple_wallet::welcome, _1),
                           tr(USAGE_WELCOME),
                           tr("为首次使用者显示 Monero 基本信息"));
  m_cmd_binder.set_handler("version",
                           boost::bind(&simple_wallet::on_command, this, &simple_wallet::version, _1),
                           tr(USAGE_VERSION),
                           tr("显示版本信息"));
  m_cmd_binder.set_handler("clear",
                           boost::bind(&simple_wallet::on_command, this, &simple_wallet::clear, _1),
                           tr(USAGE_CLEAR),
                           tr("清除控制台屏幕"));
  m_cmd_binder.set_handler("show_qr_code",
                           boost::bind(&simple_wallet::on_command, this, &simple_wallet::show_qr_code, _1),
                           tr(USAGE_SHOW_QR_CODE),
                           tr("以二维码显示地址"));
  m_cmd_binder.set_handler("help",
                           boost::bind(&simple_wallet::on_command, this, &simple_wallet::help, _1),
                           tr(USAGE_HELP),
                           tr("显示帮助内容或 <command> 的文档。"));
 m_cmd_binder.set_handler("apropos",
                           boost::bind(&simple_wallet::on_command, this, &simple_wallet::apropos, _1),
                           tr(USAGE_APROPOS),
                           tr("在所有命令说明中搜索关键词"));
 m_cmd_binder.set_handler("scan_tx",
                           boost::bind(&simple_wallet::on_command, this, &simple_wallet::scan_tx, _1),
                           tr(USAGE_SCAN_TX),
                           tr("扫描指定的 <txid> 交易，处理交易并查找输出"));
  m_cmd_binder.set_unknown_command_handler(boost::bind(&simple_wallet::on_command, this, &simple_wallet::on_unknown_command, _1));
  m_cmd_binder.set_empty_command_handler(boost::bind(&simple_wallet::on_empty_command, this));
  m_cmd_binder.set_cancel_handler(boost::bind(&simple_wallet::on_cancelled_command, this));
}
//----------------------------------------------------------------------------------------------------
bool simple_wallet::set_variable(const std::vector<std::string> &args)
{
  if (args.empty())
  {
    std::string seed_language = m_wallet->get_seed_language();
    if (m_use_english_language_names)
      seed_language = crypto::ElectrumWords::get_english_name_for(seed_language, m_wallet->is_polyseed());
    std::string priority_string = "invalid";
    const fee_priority priority = m_wallet->get_default_priority();
    priority_string = tools::fee_priority_utilities::to_string(priority);
    const auto priority_index = tools::fee_priority_utilities::as_integral(priority);
    std::string ask_password_string = "invalid";
    switch (m_wallet->ask_password())
    {
      case tools::wallet2::AskPasswordNever: ask_password_string = "never"; break;
      case tools::wallet2::AskPasswordOnAction: ask_password_string = "action"; break;
      case tools::wallet2::AskPasswordToDecrypt: ask_password_string = "decrypt"; break;
    }
    std::string setup_background_mining_string = "invalid";
    switch (m_wallet->setup_background_mining())
    {
      case tools::wallet2::BackgroundMiningMaybe: setup_background_mining_string = "maybe"; break;
      case tools::wallet2::BackgroundMiningYes: setup_background_mining_string = "yes"; break;
      case tools::wallet2::BackgroundMiningNo: setup_background_mining_string = "no"; break;
    }
    success_msg_writer() << "seed = " << seed_language;
    success_msg_writer() << "always-confirm-transfers = " << m_wallet->always_confirm_transfers();
    success_msg_writer() << "print-ring-members = " << m_wallet->print_ring_members();
    success_msg_writer() << "store-tx-info = " << m_wallet->store_tx_info();
    success_msg_writer() << "default-ring-size = " << (m_wallet->default_mixin() ? m_wallet->default_mixin() + 1 : 0);
    success_msg_writer() << "auto-refresh = " << m_wallet->auto_refresh();
    success_msg_writer() << "refresh-type = " << get_refresh_type_name(m_wallet->get_refresh_type());
    success_msg_writer() << "priority = " << priority_index << " (" << priority_string << ")";
    success_msg_writer() << "ask-password = " << m_wallet->ask_password() << " (" << ask_password_string << ")";
    success_msg_writer() << "unit = " << cryptonote::get_unit(cryptonote::get_default_decimal_point());
    success_msg_writer() << "max-reorg-depth = " << m_wallet->max_reorg_depth();
    success_msg_writer() << "min-outputs-count = " << m_wallet->get_min_output_count();
    success_msg_writer() << "min-outputs-value = " << cryptonote::print_money(m_wallet->get_min_output_value());
    success_msg_writer() << "merge-destinations = " << m_wallet->merge_destinations();
    success_msg_writer() << "confirm-backlog = " << m_wallet->confirm_backlog();
    success_msg_writer() << "confirm-backlog-threshold = " << m_wallet->get_confirm_backlog_threshold();
    success_msg_writer() << "confirm-export-overwrite = " << m_wallet->confirm_export_overwrite();
    success_msg_writer() << "refresh-from-block-height = " << m_wallet->get_refresh_from_block_height();
    success_msg_writer() << "auto-low-priority = " << m_wallet->auto_low_priority();
    success_msg_writer() << "segregate-pre-fork-outputs = " << m_wallet->segregate_pre_fork_outputs();
    success_msg_writer() << "key-reuse-mitigation2 = " << m_wallet->key_reuse_mitigation2();
    const std::pair<size_t, size_t> lookahead = m_wallet->get_subaddress_lookahead();
    success_msg_writer() << "subaddress-lookahead = " << lookahead.first << ":" << lookahead.second;
    success_msg_writer() << "segregation-height = " << m_wallet->segregation_height();
    success_msg_writer() << "ignore-fractional-outputs = " << m_wallet->ignore_fractional_outputs();
    success_msg_writer() << "ignore-outputs-above = " << cryptonote::print_money(m_wallet->ignore_outputs_above());
    success_msg_writer() << "ignore-outputs-below = " << cryptonote::print_money(m_wallet->ignore_outputs_below());
    success_msg_writer() << "track-uses = " << m_wallet->track_uses();
    success_msg_writer() << "background-sync = " << get_background_sync_type_name(m_wallet->background_sync_type());
    success_msg_writer() << "setup-background-mining = " << setup_background_mining_string;
    success_msg_writer() << "device-name = " << m_wallet->device_name();
    success_msg_writer() << "export-format = " << (m_wallet->export_format() == tools::wallet2::ExportFormat::Ascii ? "ascii" : "binary");
    success_msg_writer() << "show-wallet-name-when-locked = " << m_wallet->show_wallet_name_when_locked();
    success_msg_writer() << "inactivity-lock-timeout = " << m_wallet->inactivity_lock_timeout()
#ifdef _WIN32
        << " (disabled on Windows)"
#endif
        ;
    success_msg_writer() << "enable-multisig-experimental = " << m_wallet->is_multisig_enabled();
    return true;
  }
  else
  {
    CHECK_IF_BACKGROUND_SYNCING("cannot change wallet settings");

#define CHECK_SIMPLE_VARIABLE(name, f, help) do \
  if (args[0] == name) { \
    if (args.size() <= 1) \
    { \
      fail_msg_writer() << "set " << #name << ": " << tr("需要一个参数") << " (" << help << ")"; \
      return true; \
    } \
    else \
    { \
      f(args); \
      return true; \
    } \
  } while(0)

    if (args[0] == "seed")
    {
      if (args.size() == 1)
      {
        fail_msg_writer() << tr("set seed：需要一个参数。可用选项：language");
        return true;
      }
      else if (args[1] == "language")
      {
        seed_set_language(args);
        return true;
      }
    }
    CHECK_SIMPLE_VARIABLE("always-confirm-transfers", set_always_confirm_transfers, tr("0 or 1"));
    CHECK_SIMPLE_VARIABLE("print-ring-members", set_print_ring_members, tr("0 or 1"));
    CHECK_SIMPLE_VARIABLE("store-tx-info", set_store_tx_info, tr("0 or 1"));
    CHECK_SIMPLE_VARIABLE("auto-refresh", set_auto_refresh, tr("0 or 1"));
    CHECK_SIMPLE_VARIABLE("refresh-type", set_refresh_type, tr("full (slowest, no assumptions); optimize-coinbase (fast, assumes the whole coinbase is paid to a single address); no-coinbase (fastest, assumes we receive no coinbase transaction), default (same as optimize-coinbase)"));
    CHECK_SIMPLE_VARIABLE("priority", set_default_priority, tr("0, 1, 2, 3, or 4, or one of ") << join_priority_strings(", "));
    CHECK_SIMPLE_VARIABLE("ask-password", set_ask_password, tr("0|1|2 (or never|action|decrypt)"));
    CHECK_SIMPLE_VARIABLE("unit", set_unit, tr("monero, millinero, micronero, nanonero, piconero"));
    CHECK_SIMPLE_VARIABLE("max-reorg-depth", set_max_reorg_depth, tr("unsigned integer"));
    CHECK_SIMPLE_VARIABLE("min-outputs-count", set_min_output_count, tr("unsigned integer"));
    CHECK_SIMPLE_VARIABLE("min-outputs-value", set_min_output_value, tr("amount"));
    CHECK_SIMPLE_VARIABLE("merge-destinations", set_merge_destinations, tr("0 or 1"));
    CHECK_SIMPLE_VARIABLE("confirm-backlog", set_confirm_backlog, tr("0 or 1"));
    CHECK_SIMPLE_VARIABLE("confirm-backlog-threshold", set_confirm_backlog_threshold, tr("unsigned integer"));
    CHECK_SIMPLE_VARIABLE("confirm-export-overwrite", set_confirm_export_overwrite, tr("0 or 1"));
    CHECK_SIMPLE_VARIABLE("refresh-from-block-height", set_refresh_from_block_height, tr("block height"));
    CHECK_SIMPLE_VARIABLE("auto-low-priority", set_auto_low_priority, tr("0 or 1"));
    CHECK_SIMPLE_VARIABLE("segregate-pre-fork-outputs", set_segregate_pre_fork_outputs, tr("0 or 1"));
    CHECK_SIMPLE_VARIABLE("key-reuse-mitigation2", set_key_reuse_mitigation2, tr("0 or 1"));
    CHECK_SIMPLE_VARIABLE("subaddress-lookahead", set_subaddress_lookahead, tr("<major>:<minor>"));
    CHECK_SIMPLE_VARIABLE("segregation-height", set_segregation_height, tr("unsigned integer"));
    CHECK_SIMPLE_VARIABLE("ignore-fractional-outputs", set_ignore_fractional_outputs, tr("0 or 1"));
    CHECK_SIMPLE_VARIABLE("ignore-outputs-above", set_ignore_outputs_above, tr("amount"));
    CHECK_SIMPLE_VARIABLE("ignore-outputs-below", set_ignore_outputs_below, tr("amount"));
    CHECK_SIMPLE_VARIABLE("track-uses", set_track_uses, tr("0 or 1"));
    CHECK_SIMPLE_VARIABLE("background-sync", setup_background_sync, tr("off (default); reuse-wallet-password (reuse the wallet password to encrypt the background cache); custom-background-password (use a custom background password to encrypt the background cache)"));
    CHECK_SIMPLE_VARIABLE("show-wallet-name-when-locked", set_show_wallet_name_when_locked, tr("1 or 0"));
    CHECK_SIMPLE_VARIABLE("inactivity-lock-timeout", set_inactivity_lock_timeout, tr("unsigned integer (seconds, 0 to disable)"));
    CHECK_SIMPLE_VARIABLE("setup-background-mining", set_setup_background_mining, tr("1/yes or 0/no"));
    CHECK_SIMPLE_VARIABLE("device-name", set_device_name, tr("<device_name[:device_spec]>"));
    CHECK_SIMPLE_VARIABLE("export-format", set_export_format, tr("\"binary\" or \"ascii\""));
    CHECK_SIMPLE_VARIABLE("load-deprecated-formats", set_load_deprecated_formats, tr("0 or 1"));
    CHECK_SIMPLE_VARIABLE("enable-multisig-experimental", set_enable_multisig, tr("0 or 1"));
  }
  fail_msg_writer() << tr("set：无法识别的参数");
  return true;
}

//----------------------------------------------------------------------------------------------------
bool simple_wallet::set_log(const std::vector<std::string> &args)
{
  if(args.size() > 1)
  {
    PRINT_USAGE(USAGE_SET_LOG);
    return true;
  }
  if(!args.empty())
  {
    uint16_t level = 0;
    if(epee::string_tools::get_xtype_from_string(level, args[0]))
    {
      if(4 < level)
      {
        fail_msg_writer() << boost::format(tr("数字范围错误，请使用：%s")) % USAGE_SET_LOG;
        return true;
      }
      mlog_set_log_level(level);
    }
    else
    {
      mlog_set_log(args[0].c_str());
    }
  }
  
  success_msg_writer() << "New log categories: " << mlog_get_categories();
  return true;
}
//----------------------------------------------------------------------------------------------------
bool simple_wallet::ask_wallet_create_if_needed(const std::string &wallet_dir)
{
  LOG_PRINT_L3("simple_wallet::ask_wallet_create_if_needed() started");
  std::string wallet_path;
  std::string confirm_creation;
  bool wallet_name_valid = false;
  bool keys_file_exists;
  bool wallet_file_exists;

  do{
      LOG_PRINT_L3("User asked to specify wallet file name.");
      wallet_path = input_line(
        tr(m_restoring ? "请输入恢复钱包的新钱包文件名（例如 MyWallet）。\n"
        "钱包文件名（或按 Ctrl-C 退出）" :
        "请输入钱包文件名（例如 MyWallet）。如果钱包不存在，将创建新钱包。\n"
        "钱包文件名（或按 Ctrl-C 退出）")
      );
      if(std::cin.eof())
      {
        LOG_ERROR("Unexpected std::cin.eof() - Exited simple_wallet::ask_wallet_create_if_needed()");
        return false;
      }

      wallet_path = resolve_wallet_path(wallet_path, wallet_dir);

      if(!tools::wallet2::wallet_valid_path_format(wallet_path))
      {
        fail_msg_writer() << tr("钱包名称无效，请重试或按 Ctrl-C 退出。");
        wallet_name_valid = false;
      }
      else
      {
        tools::wallet2::wallet_exists(wallet_path, keys_file_exists, wallet_file_exists);
        LOG_PRINT_L3("wallet_path: " << wallet_path << "");
        LOG_PRINT_L3("keys_file_exists: " << std::boolalpha << keys_file_exists << std::noboolalpha
        << "  wallet_file_exists: " << std::boolalpha << wallet_file_exists << std::noboolalpha);

        if((keys_file_exists || wallet_file_exists) && (!m_generate_new.empty() || m_restoring))
        {
          fail_msg_writer() << tr("正在生成或恢复钱包，但指定的文件已存在。为避免覆盖文件，现退出。");
          return false;
        }
        if(wallet_file_exists && keys_file_exists) //Yes wallet, yes keys
        {
          success_msg_writer() << tr("已找到钱包文件和密钥文件，正在加载……");
          m_wallet_file = wallet_path;
          return true;
        }
        else if(!wallet_file_exists && keys_file_exists) //No wallet, yes keys
        {
          success_msg_writer() << tr("找到密钥文件但未找到钱包文件，正在重新生成……");
          m_wallet_file = wallet_path;
          return true;
        }
        else if(wallet_file_exists && !keys_file_exists) //Yes wallet, no keys
        {
          fail_msg_writer() << tr("未找到密钥文件，打开钱包失败：") << "\"" << wallet_path << "\". Exiting.";
          return false;
        }
        else if(!wallet_file_exists && !keys_file_exists) //No wallet, no keys
        {
          bool ok = true;
          if (!m_restoring)
          {
            message_writer() << tr("正在查找文件名：") << boost::filesystem::absolute(wallet_path);
            message_writer() << tr("未找到该名称的钱包。确认创建新钱包：") << wallet_path;
            confirm_creation = input_line("", true);
            if(std::cin.eof())
            {
              LOG_ERROR("Unexpected std::cin.eof() - Exited simple_wallet::ask_wallet_create_if_needed()");
              return false;
            }
            ok = command_line::is_yes(confirm_creation);
          }
          if (ok)
          {
            success_msg_writer() << tr("正在生成新钱包……");
            m_generate_new = wallet_path;
            return true;
          }
        }
      }
    } while(!wallet_name_valid);

  LOG_ERROR("Failed out of do-while loop in ask_wallet_create_if_needed()");
  return false;
}

/*!
 * \brief Prints the seed with a nice message
 * \param seed seed to print
 */
void simple_wallet::print_seed(const epee::wipeable_string &seed, bool as_legacy_seed, uint64_t birthday, bool is_encrypted)
{
  std::string seed_type;
  if (m_wallet->get_multisig_status().multisig_is_active)
  {
    seed_type = tr("string");
  }
  else if (m_wallet->is_polyseed() && !as_legacy_seed)
  {
    seed_type = tr("16 词 Polyseed");
  }
  else
  {
    seed_type = tr("25 词传统助记词");
  }
  success_msg_writer(true) << "\n" << boost::format(tr("NOTE: The following %s can be used to recover access to your wallet. "
    "Write this info down and store it somewhere safe and secure. Please do not store it in "
    "your email or on file storage services outside of your immediate control.\n")) % seed_type;
  if (as_legacy_seed)
  {
    success_msg_writer(true) << tr("Use the following English legacy seed, without any seed offset, to restore if you can't use the wallet's original Polyseed:\n");
  }
  // don't log
  if (m_wallet->is_polyseed())
  {
    epee::wipeable_string zero_terminated_seed(seed);
    zero_terminated_seed.push_back('\0');
    std::cout << zero_terminated_seed.data() << std::endl << std::endl;
    if (is_encrypted)
    {
      std::cout << tr("Polyseed 已使用密码短语加密，恢复钱包时必须输入该密码短语") << std::endl;
    }
    if (birthday != 0)
    {
      std::cout << tr("Polyseed 生日：") << tools::get_human_readable_timestamp(birthday) << std::endl;
    }
  }
  else
  {
    size_t len  = seed.size();
    for (const char *ptr = seed.data(); len--; ++ptr)
    {
      putchar(*ptr);
    }
    putchar('\n');
    fflush(stdout);
  }
}
//----------------------------------------------------------------------------------------------------
static bool datestr_to_int(const std::string &heightstr, uint16_t &year, uint8_t &month, uint8_t &day)
{
  if (heightstr.size() != 10 || heightstr[4] != '-' || heightstr[7] != '-')
  {
    fail_msg_writer() << tr("日期格式必须为 YYYY-MM-DD");
    return false;
  }
  try
  {
    year  = boost::lexical_cast<uint16_t>(heightstr.substr(0,4));
    // lexical_cast<uint8_t> won't work because uint8_t is treated as character type
    month = boost::lexical_cast<uint16_t>(heightstr.substr(5,2));
    day   = boost::lexical_cast<uint16_t>(heightstr.substr(8,2));
  }
  catch (const boost::bad_lexical_cast &)
  {
    fail_msg_writer() << tr("区块高度参数错误：") << heightstr;
    return false;
  }
  return true;
}
//----------------------------------------------------------------------------------------------------
bool simple_wallet::init(const boost::program_options::variables_map& vm)
{
  const epee::scope_guard scope_exit_handler([&](){
    m_electrum_seed.wipe();
  });

  const std::string wallet_dir = command_line::get_arg(vm, arg_wallet_dir);
  const bool testnet = tools::wallet2::has_testnet_option(vm);
  const bool stagenet = tools::wallet2::has_stagenet_option(vm);
  if (testnet && stagenet)
  {
    fail_msg_writer() << tr("不能同时指定 --testnet 和 --stagenet");
    return false;
  }
  const network_type nettype = testnet ? TESTNET : stagenet ? STAGENET : MAINNET;

  epee::wipeable_string multisig_keys;
  epee::wipeable_string password;
  epee::wipeable_string seed_pass;

  if (!handle_command_line(vm))
    return false;

  bool welcome = false;

  if((!m_generate_new.empty()) + (!m_wallet_file.empty()) + (!m_generate_from_device.empty()) + (!m_generate_from_view_key.empty()) + (!m_generate_from_spend_key.empty()) + (!m_generate_from_keys.empty()) + (!m_generate_from_multisig_keys.empty()) + (!m_generate_from_json.empty()) > 1)
  {
    fail_msg_writer() << tr("can't specify more than one of --generate-new-wallet=\"wallet_name\", --wallet-file=\"wallet_name\", --generate-from-view-key=\"wallet_name\", --generate-from-spend-key=\"wallet_name\", --generate-from-keys=\"wallet_name\", --generate-from-multisig-keys=\"wallet_name\", --generate-from-json=\"jsonfilename\" and --generate-from-device=\"wallet_name\"");
    return false;
  }
  else if (m_generate_new.empty() && m_wallet_file.empty() && m_generate_from_device.empty() && m_generate_from_view_key.empty() && m_generate_from_spend_key.empty() && m_generate_from_keys.empty() && m_generate_from_multisig_keys.empty() && m_generate_from_json.empty())
  {
    if(!ask_wallet_create_if_needed(wallet_dir)) return false;
  }

  bool enable_multisig = false;
  if (m_restore_multisig_wallet) {
    fail_msg_writer() << tr("多重签名功能已禁用。");
    fail_msg_writer() << tr("多重签名功能仍处于实验阶段，可能存在错误。可能出现的问题包括：发送到多重签名钱包的资金完全无法使用，只能在恶意成员参与的情况下使用，或被恶意成员窃取。");
    if (!command_line::is_yes(input_line("Do you want to continue restoring a multisig wallet?", true))) {
      message_writer() << tr("您已取消恢复多重签名钱包。");
      return false;
    }
    enable_multisig = true;
  }

  if (!m_generate_new.empty() || m_restoring)
  {
    if (!m_subaddress_lookahead.empty() && !parse_subaddress_lookahead(m_subaddress_lookahead))
      return false;

    std::string old_language;
    bool is_polyseed = !m_restoring && !m_non_deterministic && !m_use_legacy_seed;
    polyseed::data polyseed(POLYSEED_MONERO);

    // check for recover flag.  if present, require electrum word list (only recovery option for now).
    if (m_restore_deterministic_wallet || m_restore_multisig_wallet)
    {
      if (m_non_deterministic)
      {
        fail_msg_writer() << tr("不能同时指定 --restore-deterministic-wallet 或 --restore-multisig-wallet 与 --non-deterministic");
        return false;
      }
      if (!m_wallet_file.empty())
      {
        if (m_restore_multisig_wallet)
          fail_msg_writer() << tr("--restore-multisig-wallet 使用 --generate-new-wallet，而不是 --wallet-file");
        else
          fail_msg_writer() << tr("--restore-deterministic-wallet 使用 --generate-new-wallet，而不是 --wallet-file");
        return false;
      }

      if (m_electrum_seed.empty())
      {
        if (m_restore_multisig_wallet)
        {
            const char *prompt = "Specify multisig seed";
            m_electrum_seed = input_secure_line(prompt);
            if (std::cin.eof())
              return false;
            if (m_electrum_seed.empty())
            {
              fail_msg_writer() << tr("请使用 --electrum-seed=“此处填写多重签名助记词” 指定恢复参数");
              return false;
            }
        }
        else
        {
          m_electrum_seed = "";
          const char *prompt = "Specify Electrum seed";
          epee::wipeable_string electrum_seed = input_secure_line(prompt);
          if (std::cin.eof())
            return false;
          if (electrum_seed.empty())
          {
            fail_msg_writer() << tr("请使用 --electrum-seed=“此处填写助记词列表” 指定恢复参数");
            return false;
          }
          m_electrum_seed = electrum_seed;
        }
      }

      if (m_restore_multisig_wallet)
      {
        const boost::optional<epee::wipeable_string> parsed = m_electrum_seed.parse_hexstr();
        if (!parsed)
        {
          fail_msg_writer() << tr("多重签名助记词验证失败");
          return false;
        }
        multisig_keys = *parsed;
      }
      else
      {
        if (!crypto::ElectrumWords::words_to_bytes_ex(m_electrum_seed, m_recovery_key, old_language, is_polyseed, polyseed))
        {
          fail_msg_writer() << tr("Electrum 风格助记词列表验证失败");
          return false;
        }
      }

      auto pwd_container = password_prompter(tr("请输入种子偏移密码短语；没有则留空"), false);
      if (std::cin.eof() || !pwd_container)
        return false;
      seed_pass = pwd_container->password();
      if (is_polyseed && !seed_pass.empty())
      {
        message_writer(console_color_red, false) << tr("再次恢复钱包时必须重新输入此密码短语。");
        message_writer(console_color_red, false) << tr("该密码短语不会保存，也无法在应用中再次显示。");
        message_writer(console_color_red, false) << tr("错误的密码短语不会被检测出来，只会导致生成另一个不同的钱包。");
      }
      if (!seed_pass.empty() && !m_restore_multisig_wallet)
        m_recovery_key = cryptonote::decrypt_key(m_recovery_key, seed_pass);
    }
    if (!m_generate_from_view_key.empty())
    {
      m_wallet_file = resolve_wallet_path(m_generate_from_view_key, wallet_dir);
      // parse address
      std::string address_string = input_line("Standard address");
      if (std::cin.eof())
        return false;
      if (address_string.empty()) {
        fail_msg_writer() << tr("未提供数据，已取消");
        return false;
      }
      cryptonote::address_parse_info info;
      if(!get_account_address_from_str(info, nettype, address_string))
      {
          fail_msg_writer() << tr("解析地址失败");
          return false;
      }
      if (info.is_subaddress)
      {
        fail_msg_writer() << tr("此地址是子地址，不能在此处使用。");
        return false;
      }

      // parse view secret key
      epee::wipeable_string viewkey_string = input_secure_line("Secret view key");
      if (std::cin.eof())
        return false;
      if (viewkey_string.empty()) {
        fail_msg_writer() << tr("未提供数据，已取消");
        return false;
      }
      crypto::secret_key viewkey;
      if (!viewkey_string.hex_to_pod(unwrap(unwrap(viewkey))))
      {
        fail_msg_writer() << tr("解析查看私钥失败");
        return false;
      }

      // check the view key matches the given address
      crypto::public_key pkey;
      if (!crypto::secret_key_to_public_key(viewkey, pkey)) {
        fail_msg_writer() << tr("验证查看私钥失败");
        return false;
      }
      if (info.address.m_view_public_key != pkey) {
        fail_msg_writer() << tr("查看密钥与标准地址不匹配");
        return false;
      }

      auto r = new_wallet(vm, info.address, boost::none, viewkey);
      CHECK_AND_ASSERT_MES(r, false, tr("创建账户失败"));
      password = *r;
      welcome = true;
    }
    else if (!m_generate_from_spend_key.empty())
    {
      m_wallet_file = resolve_wallet_path(m_generate_from_spend_key, wallet_dir);
      // parse spend secret key
      epee::wipeable_string spendkey_string = input_secure_line("Secret spend key");
      if (std::cin.eof())
        return false;
      if (spendkey_string.empty()) {
        fail_msg_writer() << tr("未提供数据，已取消");
        return false;
      }
      if (!spendkey_string.hex_to_pod(unwrap(unwrap(m_recovery_key))))
      {
        fail_msg_writer() << tr("解析支出私钥失败");
        return false;
      }
      auto r = new_wallet(vm, m_recovery_key, true, false, "", false, polyseed, seed_pass);
      CHECK_AND_ASSERT_MES(r, false, tr("创建账户失败"));
      password = *r;
      welcome = true;
    }
    else if (!m_generate_from_keys.empty())
    {
      m_wallet_file = resolve_wallet_path(m_generate_from_keys, wallet_dir);
      // parse address
      std::string address_string = input_line("Standard address");
      if (std::cin.eof())
        return false;
      if (address_string.empty()) {
        fail_msg_writer() << tr("未提供数据，已取消");
        return false;
      }
      cryptonote::address_parse_info info;
      if(!get_account_address_from_str(info, nettype, address_string))
      {
          fail_msg_writer() << tr("解析地址失败");
          return false;
      }
      if (info.is_subaddress)
      {
        fail_msg_writer() << tr("此地址是子地址，不能在此处使用。");
        return false;
      }

      // parse spend secret key
      epee::wipeable_string spendkey_string = input_secure_line("Secret spend key");
      if (std::cin.eof())
        return false;
      if (spendkey_string.empty()) {
        fail_msg_writer() << tr("未提供数据，已取消");
        return false;
      }
      crypto::secret_key spendkey;
      if (!spendkey_string.hex_to_pod(unwrap(unwrap(spendkey))))
      {
        fail_msg_writer() << tr("解析支出私钥失败");
        return false;
      }

      // parse view secret key
      epee::wipeable_string viewkey_string = input_secure_line("Secret view key");
      if (std::cin.eof())
        return false;
      if (viewkey_string.empty()) {
        fail_msg_writer() << tr("未提供数据，已取消");
        return false;
      }
      crypto::secret_key viewkey;
      if(!viewkey_string.hex_to_pod(unwrap(unwrap(viewkey))))
      {
        fail_msg_writer() << tr("解析查看私钥失败");
        return false;
      }

      // check the spend and view keys match the given address
      crypto::public_key pkey;
      if (!crypto::secret_key_to_public_key(spendkey, pkey)) {
        fail_msg_writer() << tr("验证支出私钥失败");
        return false;
      }
      if (info.address.m_spend_public_key != pkey) {
        fail_msg_writer() << tr("支出密钥与标准地址不匹配");
        return false;
      }
      if (!crypto::secret_key_to_public_key(viewkey, pkey)) {
        fail_msg_writer() << tr("验证查看私钥失败");
        return false;
      }
      if (info.address.m_view_public_key != pkey) {
        fail_msg_writer() << tr("查看密钥与标准地址不匹配");
        return false;
      }
      auto r = new_wallet(vm, info.address, spendkey, viewkey);
      CHECK_AND_ASSERT_MES(r, false, tr("创建账户失败"));
      password = *r;
      welcome = true;
    }
    
    // Asks user for all the data required to merge secret keys from multisig wallets into one master wallet, which then gets full control of the multisig wallet. The resulting wallet will be the same as any other regular wallet.
    else if (!m_generate_from_multisig_keys.empty())
    {
      m_wallet_file = resolve_wallet_path(m_generate_from_multisig_keys, wallet_dir);
      unsigned int multisig_m;
      unsigned int multisig_n;
      
      // parse multisig type
      std::string multisig_type_string = input_line("多重签名 type (input as M/N with M <= N and M > 1)");
      if (std::cin.eof())
        return false;
      if (multisig_type_string.empty())
      {
        fail_msg_writer() << tr("未提供数据，已取消");
        return false;
      }
      if (sscanf(multisig_type_string.c_str(), "%u/%u", &multisig_m, &multisig_n) != 2)
      {
        fail_msg_writer() << tr("错误：expected M/N, but got: ") << multisig_type_string;
        return false;
      }
      if (multisig_m <= 1 || multisig_m > multisig_n)
      {
        fail_msg_writer() << tr("错误：expected M > 1 and M <= N, but got: ") << multisig_type_string;
        return false;
      }
      if (multisig_m != multisig_n)
      {
        fail_msg_writer() << tr("错误：M/N is currently unsupported. ");
        return false;
      }      
      message_writer() << boost::format(tr("正在从 %u/%u 个多重签名钱包密钥生成主钱包")) % multisig_m % multisig_n;
      
      // parse multisig address
      std::string address_string = input_line("多重签名 wallet address");
      if (std::cin.eof())
        return false;
      if (address_string.empty()) {
        fail_msg_writer() << tr("未提供数据，已取消");
        return false;
      }
      cryptonote::address_parse_info info;
      if(!get_account_address_from_str(info, nettype, address_string))
      {
          fail_msg_writer() << tr("解析地址失败");
          return false;
      }
      
      // parse secret view key
      epee::wipeable_string viewkey_string = input_secure_line("Secret view key");
      if (std::cin.eof())
        return false;
      if (viewkey_string.empty())
      {
        fail_msg_writer() << tr("未提供数据，已取消");
        return false;
      }
      crypto::secret_key viewkey;
      if(!viewkey_string.hex_to_pod(unwrap(unwrap(viewkey))))
      {
        fail_msg_writer() << tr("解析私有视图密钥失败");
        return false;
      }
      
      // check that the view key matches the given address
      crypto::public_key pkey;
      if (!crypto::secret_key_to_public_key(viewkey, pkey))
      {
        fail_msg_writer() << tr("验证私有视图密钥失败");
        return false;
      }
      if (info.address.m_view_public_key != pkey)
      {
        fail_msg_writer() << tr("查看密钥与标准地址不匹配");
        return false;
      }
      
      // parse multisig spend keys
      crypto::secret_key spendkey;
      // parsing N/N
      if(multisig_m == multisig_n)
      {
        std::vector<crypto::secret_key> multisig_secret_spendkeys(multisig_n);
        epee::wipeable_string spendkey_string;
        cryptonote::blobdata spendkey_data;
        // get N secret spend keys from user
        for(unsigned int i=0; i<multisig_n; ++i)
        {
          spendkey_string = input_secure_line(tr((boost::format(tr("私有支出密钥（%u/%u）")) % (i+1) % multisig_m).str().c_str()));
          if (std::cin.eof())
            return false;
          if (spendkey_string.empty())
          {
            fail_msg_writer() << tr("未提供数据，已取消");
            return false;
          }
          if(!spendkey_string.hex_to_pod(unwrap(unwrap(multisig_secret_spendkeys[i]))))
          {
            fail_msg_writer() << tr("解析支出私钥失败");
            return false;
          }
        }
        
        // sum the spend keys together to get the master spend key
        spendkey = multisig_secret_spendkeys[0];
        for(unsigned int i=1; i<multisig_n; ++i)
          sc_add(reinterpret_cast<unsigned char*>(&spendkey), reinterpret_cast<unsigned char*>(&spendkey), reinterpret_cast<unsigned char*>(&multisig_secret_spendkeys[i]));
      }
      // parsing M/N
      else
      {
        fail_msg_writer() << tr("错误：M/N is currently unsupported");
        return false;
      }
      
      // check that the spend key matches the given address
      if (!crypto::secret_key_to_public_key(spendkey, pkey))
      {
        fail_msg_writer() << tr("验证支出私钥失败");
        return false;
      }
      if (info.address.m_spend_public_key != pkey)
      {
        fail_msg_writer() << tr("支出密钥与标准地址不匹配");
        return false;
      }
      
      // create wallet
      auto r = new_wallet(vm, info.address, spendkey, viewkey);
      CHECK_AND_ASSERT_MES(r, false, tr("创建账户失败"));
      password = *r;
      welcome = true;
    }
    
    else if (!m_generate_from_json.empty())
    {
      try
      {
        auto rc = tools::wallet2::make_from_json(vm, false, m_generate_from_json, password_prompter);
        m_wallet = std::move(rc.first);
        password = rc.second.password();
        if (!m_wallet) return false;
        m_wallet_file = m_wallet->path();
      }
      catch (const std::exception &e)
      {
        fail_msg_writer() << e.what();
        return false;
      }
    }
    else if (!m_generate_from_device.empty())
    {
      m_wallet_file = resolve_wallet_path(m_generate_from_device, wallet_dir);
      // create wallet
      auto r = new_wallet(vm);
      CHECK_AND_ASSERT_MES(r, false, tr("创建账户失败"));
      password = *r;
      welcome = true;
      // if no block_height or date is specified, assume it's a new account and start it "now"
      if (command_line::is_arg_defaulted(vm, arg_restore_height) && command_line::is_arg_defaulted(vm, arg_restore_date)) {
        {
          tools::scoped_message_writer wrt = tools::msg_writer();
          wrt << tr("未指定恢复高度。") << " ";
          wrt << tr("将按创建新账户处理，恢复将从当前估算的区块高度开始。") << " ";
          wrt << tr("如需从特定高度恢复已有账户，请使用 --restore-height 或 --restore-date。");
        }
        std::string confirm = input_line(tr("确认继续吗？"), true);
        if (std::cin.eof()) CHECK_AND_ASSERT_MES(false, false, tr("已中止创建账户"));

        if (command_line::is_yes(confirm))
        {
          m_wallet->set_refresh_from_block_height(m_wallet->estimate_blockchain_height() > 0 ? m_wallet->estimate_blockchain_height() - 1 : 0);
          m_wallet->explicit_refresh_from_block_height(true);
          m_restore_height = m_wallet->get_refresh_from_block_height();
        }
        else
        {
          m_wallet->explicit_refresh_from_block_height(false);
        }
      }
      else if (command_line::is_arg_defaulted(vm, arg_restore_height) && !command_line::is_arg_defaulted(vm, arg_restore_date))
      {
        uint16_t year;
        uint8_t month, day;
        if (!datestr_to_int(m_restore_date, year, month, day)) return false;
        try
        {
          m_restore_height = m_wallet->get_blockchain_height_by_date(year, month, day);
          success_msg_writer() << tr("恢复高度为：") << m_restore_height;
          m_wallet->explicit_refresh_from_block_height(true);
        }
        catch (const std::runtime_error& e)
        {
          message_writer(console_color_yellow, true) << tr("无法连接到守护进程，将 --restore-date 转换为恢复高度失败：") << e.what();
          message_writer(console_color_yellow, true) << tr("恢复高度为：") << m_restore_height;
        }
      }
    }
    else
    {
      if (m_generate_new.empty()) {
        fail_msg_writer() << tr("请使用 --generate-new-wallet 指定钱包路径（不要使用 --wallet-file）");
        return false;
      }
      m_wallet_file = resolve_wallet_path(m_generate_new, wallet_dir);
      boost::optional<epee::wipeable_string> r;
      if (m_restore_multisig_wallet)
        r = new_wallet(vm, multisig_keys, seed_pass, old_language);
      else
        r = new_wallet(vm, m_recovery_key, m_restore_deterministic_wallet, m_non_deterministic, old_language, is_polyseed, polyseed, seed_pass);
      CHECK_AND_ASSERT_MES(r, false, tr("创建账户失败"));
      password = *r;
      welcome = true;
    }

    if (m_restoring && m_generate_from_json.empty() && m_generate_from_device.empty())
    {
      bool restore_height_defaulted = command_line::is_arg_defaulted(vm, arg_restore_height);
      bool restore_date_defaulted = command_line::is_arg_defaulted(vm, arg_restore_date);
      m_wallet->explicit_refresh_from_block_height(!restore_height_defaulted || !restore_date_defaulted || is_polyseed);
        
      uint64_t polyseed_restore_height = 0;
      bool is_override = false;

      if (is_polyseed)
      {
        polyseed_restore_height = m_wallet->estimate_blockchain_height(polyseed.birthday());
        if (!restore_height_defaulted || !restore_date_defaulted)
        {
          is_override = true;
          message_writer(console_color_red, true) <<
            boost::format(tr("--restore-height or --restore-date parameter value overrides restore height %u from Polyseed birthday")) % polyseed_restore_height;
          message_writer(console_color_red, true) <<
            tr("使用 Polyseed 时无需指定恢复高度，通常也不需要指定任何恢复高度");
        }
        else
        {
          m_restore_height = polyseed_restore_height;
        }
      }

      if (restore_height_defaulted && !restore_date_defaulted)
      {
        uint16_t year;
        uint8_t month;
        uint8_t day;
        if (!datestr_to_int(m_restore_date, year, month, day))
          return false;
        try
        {
          m_restore_height = m_wallet->get_blockchain_height_by_date(year, month, day);
          success_msg_writer() << tr("恢复高度为：") << m_restore_height;
        }
        catch (const std::runtime_error& e)
        {
          fail_msg_writer() << e.what();
          return false;
        }
      }

      if (is_override && m_restore_height > polyseed_restore_height)
      {
          message_writer(console_color_red, true) <<
            boost::format(tr("恢复高度 %u is higher than the restore height from Polyseed birthday, make sure to not miss any transfers")) % m_restore_height;
      }
    }
    if (!m_wallet->explicit_refresh_from_block_height() && m_restoring)
    {
      uint32_t version;
      bool connected = try_connect_to_daemon(false, &version);
      while (true)
      {
        std::string heightstr;
        if (!connected || version < MAKE_CORE_RPC_VERSION(1, 6))
          heightstr = input_line("从指定区块高度恢复 (optional, default 0)");
        else
          heightstr = input_line("从指定区块高度恢复 (optional, default 0),\nor alternatively from specific date (YYYY-MM-DD)");
        if (std::cin.eof())
          return false;
        if (heightstr.empty())
        {
          m_restore_height = 0;
          break;
        }
        try
        {
          m_restore_height = boost::lexical_cast<uint64_t>(heightstr);
          break;
        }
        catch (const boost::bad_lexical_cast &)
        {
          if (!connected || version < MAKE_CORE_RPC_VERSION(1, 6))
          {
            fail_msg_writer() << tr("m_restore_height 参数错误：") << heightstr;
            continue;
          }
          uint16_t year;
          uint8_t month;  // 1, 2, ..., 12
          uint8_t day;    // 1, 2, ..., 31
          try
          {
            if (!datestr_to_int(heightstr, year, month, day))
              return false;
            m_restore_height = m_wallet->get_blockchain_height_by_date(year, month, day);
            success_msg_writer() << tr("恢复高度为：") << m_restore_height;
            std::string confirm = input_line(tr("确认继续吗？"), true);
            if (std::cin.eof())
              return false;
            if(command_line::is_yes(confirm))
              break;
          }
          catch (const boost::bad_lexical_cast &)
          {
            fail_msg_writer() << tr("m_restore_height 参数错误：") << heightstr;
          }
          catch (const std::runtime_error& e)
          {
            fail_msg_writer() << e.what();
          }
        }
      }
    }
    if (m_restoring)
    {
      uint64_t estimate_height = m_wallet->estimate_blockchain_height();
      if (m_restore_height >= estimate_height)
      {
        success_msg_writer() << tr("恢复高度 ") << m_restore_height << ("尚未达到。当前预计区块高度为 ") << estimate_height;
        std::string confirm = input_line(tr("仍然应用恢复高度？"), true);
        if (std::cin.eof() || command_line::is_no(confirm))
          m_restore_height = 0;
      }
      m_wallet->set_refresh_from_block_height(m_restore_height);
    }
    if (enable_multisig)
      m_wallet->enable_multisig(true);
    m_wallet->rewrite(m_wallet_file, password);
  }
  else
  {
    assert(!m_wallet_file.empty());
    m_wallet_file = resolve_wallet_path(m_wallet_file, wallet_dir);
    if (!m_subaddress_lookahead.empty())
    {
      fail_msg_writer() << tr("can't specify --subaddress-lookahead and --wallet-file at the same time");
      return false;
    }
    auto r = open_wallet(vm);
    CHECK_AND_ASSERT_MES(r, false, tr("打开账户失败"));
    password = *r;
  }
  if (!m_wallet)
  {
    fail_msg_writer() << tr("钱包为空");
    return false;
  }

  if (!m_wallet->is_trusted_daemon())
  {
    message_writer(console_color_red, true) << (boost::format(tr("警告：正在使用不受信任的守护进程 %s")) % m_wallet->get_daemon_address()).str();
    message_writer(console_color_red, true) << boost::format(tr("使用第三方守护进程可能损害您的安全和隐私"));
    bool ssl = false;
    if (m_wallet->check_connection(NULL, &ssl) && !ssl)
      message_writer(console_color_red, true) << boost::format(tr("使用自己的节点但不启用 SSL，会使 RPC 流量暴露给监控"));
    message_writer(console_color_red, true) << boost::format(tr("强烈建议使用自己的守护进程连接 Monero 网络"));
    message_writer(console_color_red, true) << boost::format(tr("If you or someone you trust are operating this daemon, you can use --trusted-daemon"));
  }

  if (m_wallet->get_ring_database().empty())
    fail_msg_writer() << tr("初始化环数据库失败：隐私增强功能将不可用");

  m_wallet->callback(this);

  bool skip_check_backround_mining = !command_line::get_arg(vm, arg_command).empty();
  if (!skip_check_backround_mining)
    check_background_mining(password);

  if (welcome)
    message_writer(console_color_yellow, true) << tr("如果您刚接触 Monero，请输入“welcome”查看简要介绍。");

  m_last_activity_time = time(NULL);
  return true;
}
//----------------------------------------------------------------------------------------------------
bool simple_wallet::deinit()
{
  if (!m_wallet.get())
    return true;

  return close_wallet();
}
//----------------------------------------------------------------------------------------------------
bool simple_wallet::handle_command_line(const boost::program_options::variables_map& vm)
{
  m_wallet_file                   = command_line::get_arg(vm, arg_wallet_file);
  m_generate_new                  = command_line::get_arg(vm, arg_generate_new_wallet);
  m_generate_from_device          = command_line::get_arg(vm, arg_generate_from_device);
  m_generate_from_view_key        = command_line::get_arg(vm, arg_generate_from_view_key);
  m_generate_from_spend_key       = command_line::get_arg(vm, arg_generate_from_spend_key);
  m_generate_from_keys            = command_line::get_arg(vm, arg_generate_from_keys);
  m_generate_from_multisig_keys   = command_line::get_arg(vm, arg_generate_from_multisig_keys);
  m_generate_from_json            = command_line::get_arg(vm, arg_generate_from_json);
  m_mnemonic_language             = command_line::get_arg(vm, arg_mnemonic_language);
  m_electrum_seed                 = command_line::get_arg(vm, arg_electrum_seed);
  m_restore_deterministic_wallet  = command_line::get_arg(vm, arg_restore_deterministic_wallet) || command_line::get_arg(vm, arg_restore_from_seed);
  m_restore_multisig_wallet       = command_line::get_arg(vm, arg_restore_multisig_wallet);
  m_non_deterministic             = command_line::get_arg(vm, arg_non_deterministic);
  m_restore_height                = command_line::get_arg(vm, arg_restore_height);
  m_restore_date                  = command_line::get_arg(vm, arg_restore_date);
  m_use_legacy_seed               = command_line::get_arg(vm, arg_use_legacy_seed);
  m_do_not_relay                  = command_line::get_arg(vm, arg_do_not_relay);
  m_subaddress_lookahead          = command_line::get_arg(vm, arg_subaddress_lookahead);
  m_use_english_language_names    = command_line::get_arg(vm, arg_use_english_language_names);
  m_restoring                     = !m_generate_from_view_key.empty() ||
                                    !m_generate_from_spend_key.empty() ||
                                    !m_generate_from_keys.empty() ||
                                    !m_generate_from_multisig_keys.empty() ||
                                    !m_generate_from_json.empty() ||
                                    !m_generate_from_device.empty() ||
                                    m_restore_deterministic_wallet ||
                                    m_restore_multisig_wallet;

  if (!command_line::is_arg_defaulted(vm, arg_restore_date))
  {
    uint16_t year;
    uint8_t month, day;
    if (!datestr_to_int(m_restore_date, year, month, day))
      return false;
  }

  return true;
}
//----------------------------------------------------------------------------------------------------
bool simple_wallet::try_connect_to_daemon(bool silent, uint32_t* version)
{
  uint32_t version_ = 0;
  if (!version)
    version = &version_;
  bool wallet_is_outdated = false, daemon_is_outdated = false;
  if (!m_wallet->check_connection(version, NULL, 200000, &wallet_is_outdated, &daemon_is_outdated))
  {
    if (!silent)
    {
      if (m_wallet->is_offline())
        fail_msg_writer() << tr("钱包无法连接到守护进程，因为当前处于离线模式");
      else if (wallet_is_outdated)
        fail_msg_writer() << tr("钱包无法连接到守护进程，因为钱包版本不是最新版本。") <<
          tr("请确保您运行的是最新版本的钱包。");
      else if (daemon_is_outdated)
        fail_msg_writer() << tr("钱包连接守护进程失败：") << m_wallet->get_daemon_address() << ". " <<
          tr("守护进程不是最新版本。 "
          "Please make sure the daemon is running the latest version or change the daemon address using the 'set_daemon' command.");
      else
        fail_msg_writer() << tr("钱包连接守护进程失败：") << m_wallet->get_daemon_address() << ". " <<
          boost::format(tr("守护进程未启动，或者指定了错误的端口。 "
          "Please make sure a %sdaemon is running or change the daemon address using the 'set_daemon' command."))
            % (m_wallet->nettype() == TESTNET ? "testnet " : m_wallet->nettype() == STAGENET ? "stagenet " : "");
    }
    return false;
  }
  if (!m_wallet->is_mismatched_daemon_version_allowed() && ((*version >> 16) != CORE_RPC_VERSION_MAJOR))
  {
    if (!silent)
      fail_msg_writer() << boost::format(tr("Daemon uses a different RPC major version (%u) than the wallet (%u): %s. Either update one of them, or use --allow-mismatched-daemon-version.")) % (*version>>16) % CORE_RPC_VERSION_MAJOR % m_wallet->get_daemon_address();
    return false;
  }
  return true;
}

/*!
 * \brief Gets the word seed language from the user.
 * 
 * User is asked to choose from a list of supported languages.
 * 
 * \return The chosen language.
 */
std::string simple_wallet::get_mnemonic_language(bool polyseed)
{
  std::vector<std::string> language_list_self, language_list_english;
  const std::vector<std::string> &language_list = m_use_english_language_names ? language_list_english : language_list_self;
  std::string language_choice;
  int language_number = -1;
  crypto::ElectrumWords::get_language_list(language_list_self, false, polyseed);
  crypto::ElectrumWords::get_language_list(language_list_english, true, polyseed);
  std::cout << tr("钱包助记词可用语言列表：") << std::endl;
  std::cout << tr("如果显示界面卡住，请按 ^C 退出，然后使用 --use-english-language-names 重新运行") << std::endl;
  int ii;
  std::vector<std::string>::const_iterator it;
  for (it = language_list.begin(), ii = 0; it != language_list.end(); it++, ii++)
  {
    std::cout << ii << " : " << *it << std::endl;
  }
  while (language_number < 0)
  {
    language_choice = input_line(tr("请输入您选择的语言编号"));
    if (std::cin.eof())
      return std::string();
    try
    {
      language_number = std::stoi(language_choice);
      if (!((language_number >= 0) && (static_cast<unsigned int>(language_number) < language_list.size())))
      {
        language_number = -1;
        fail_msg_writer() << tr("输入的语言编号无效，请重试。\n");
      }
    }
    catch (const std::exception &e)
    {
      fail_msg_writer() << tr("输入的语言编号无效，请重试。\n");
    }
  }
  return language_list_self[language_number];
}
//----------------------------------------------------------------------------------------------------
boost::optional<tools::password_container> simple_wallet::get_and_verify_password(bool *read_failed) const
{
  if (read_failed) *read_failed = false;
  const bool verify = m_wallet_file.empty();
  auto pwd_container = (m_wallet->is_background_wallet() && m_wallet->background_sync_type() == tools::wallet2::BackgroundSyncCustomPassword)
    ? background_sync_cache_password_prompter(verify)
    : default_password_prompter(verify);
  if (!pwd_container)
  {
    if (read_failed) *read_failed = true;
    return boost::none;
  }

  if (!m_wallet->verify_password(pwd_container->password()))
  {
    fail_msg_writer() << tr("密码无效");
    return boost::none;
  }
  return pwd_container;
}
//----------------------------------------------------------------------------------------------------
boost::optional<epee::wipeable_string> simple_wallet::new_wallet(const boost::program_options::variables_map& vm,
  const crypto::secret_key& recovery_key, bool recover, bool two_random, const std::string &old_language,
  bool is_polyseed, polyseed::data &polyseed, const epee::wipeable_string &seed_pass)
{
  std::pair<std::unique_ptr<tools::wallet2>, tools::password_container> rc;
  try { rc = tools::wallet2::make_new(vm, false, password_prompter); }
  catch(const std::exception &e) { fail_msg_writer() << tr("创建钱包失败：") << e.what(); return {}; }
  m_wallet = std::move(rc.first);
  if (!m_wallet)
  {
    return {};
  }
  epee::wipeable_string password = rc.second.password();

  if (!m_subaddress_lookahead.empty())
  {
    auto lookahead = parse_subaddress_lookahead(m_subaddress_lookahead);
    assert(lookahead);
    m_wallet->set_subaddress_lookahead(lookahead->first, lookahead->second);
  }

  bool was_deprecated_wallet = m_restore_deterministic_wallet && ((old_language == crypto::ElectrumWords::old_language_name) ||
    crypto::ElectrumWords::get_is_old_style_seed(m_electrum_seed));

  std::string mnemonic_language = old_language;

  // Check for mnemonic language from command line argument
  std::vector<std::string> language_list;
  crypto::ElectrumWords::get_language_list(language_list, false, is_polyseed);
  if (mnemonic_language.empty() && std::find(language_list.begin(), language_list.end(), m_mnemonic_language) != language_list.end())
  {
    mnemonic_language = m_mnemonic_language;
  }

  // Ask for seed language if:
  // it's a deterministic wallet AND
  // a seed language is not already specified AND
  // (it is not a wallet restore OR if it was a deprecated wallet
  // that was earlier used before this restore)
  if ((!two_random) && (mnemonic_language.empty() || mnemonic_language == crypto::ElectrumWords::old_language_name) && (!m_restore_deterministic_wallet || was_deprecated_wallet))
  {
    if (was_deprecated_wallet)
    {
      // The user had used an older version of the wallet with old style mnemonics.
      message_writer(console_color_green, false) << "\n" << tr("You had been using "
        "a deprecated version of the wallet. Please use the new seed that we provide.\n");
    }
    mnemonic_language = get_mnemonic_language(is_polyseed);
    if (mnemonic_language.empty())
      return {};
  }

  m_wallet->set_seed_language(mnemonic_language);

  bool create_address_file = command_line::get_arg(vm, arg_create_address_file);

  crypto::secret_key recovery_val;
  try
  {
    if (is_polyseed)
    {
      if (!recover)
      {
        polyseed.create(0, polyseed::get_lang_by_name(mnemonic_language));
      }
      m_wallet->generate(m_wallet_file, std::move(rc.second).password(), polyseed, seed_pass, recover, m_restore_height, create_address_file);
    }
    else {
      recovery_val = m_wallet->generate(m_wallet_file, std::move(rc.second).password(), recovery_key, recover, two_random, create_address_file);
    }
    message_writer(console_color_white, true) << tr("新钱包已生成：")
      << m_wallet->get_account().get_public_address_str(m_wallet->nettype());
    PAUSE_READLINE();
    std::cout << tr("视图密钥：");
    print_secret_key(m_wallet->get_account().get_keys().m_view_secret_key);
    putchar('\n');
  }
  catch (const std::exception& e)
  {
    fail_msg_writer() << tr("生成新钱包失败：") << e.what();
    return {};
  }

  // convert rng value to electrum-style word list
  epee::wipeable_string electrum_words;

  if (is_polyseed)
  {
    polyseed::language polyseed_language = polyseed::get_lang_by_name(mnemonic_language);
    polyseed.encode(polyseed_language, electrum_words);
  }
  else
  {
    crypto::ElectrumWords::bytes_to_words(recovery_val, electrum_words, mnemonic_language);
  }

  success_msg_writer() <<
    "**********************************************************************\n" <<
    tr("Your wallet has been generated!\n"
    "To start synchronizing with the daemon, use the \"refresh\" command.\n"
    "Use the \"help\" command to see a simplified list of available commands.\n"
    "Use \"help all\" command to see the list of all available commands.\n"
    "Use \"help <command>\" to see a command's documentation.\n"
    "Always use the \"exit\" command when closing monero-wallet-cli to save \n"
    "your current session's state. Otherwise, you might need to synchronize \n"
    "your wallet again (your wallet keys are NOT at risk in any case).\n")
  ;
  success_msg_writer() << tr("文件名：") << boost::filesystem::absolute(m_wallet->get_keys_file());

  if (!two_random)
  {
    print_seed(electrum_words, false, 0, false);
  }
  success_msg_writer() << "**********************************************************************";

  return password;
}
//----------------------------------------------------------------------------------------------------
boost::optional<epee::wipeable_string> simple_wallet::new_wallet(const boost::program_options::variables_map& vm,
  const cryptonote::account_public_address& address, const boost::optional<crypto::secret_key>& spendkey,
  const crypto::secret_key& viewkey)
{
  std::pair<std::unique_ptr<tools::wallet2>, tools::password_container> rc;
  try { rc = tools::wallet2::make_new(vm, false, password_prompter); }
  catch(const std::exception &e) { fail_msg_writer() << tr("创建钱包失败：") << e.what(); return {}; }
  m_wallet = std::move(rc.first);
  if (!m_wallet)
  {
    return {};
  }
  epee::wipeable_string password = rc.second.password();

  if (!m_subaddress_lookahead.empty())
  {
    auto lookahead = parse_subaddress_lookahead(m_subaddress_lookahead);
    assert(lookahead);
    m_wallet->set_subaddress_lookahead(lookahead->first, lookahead->second);
  }

  if (m_restore_height)
    m_wallet->set_refresh_from_block_height(m_restore_height);

  bool create_address_file = command_line::get_arg(vm, arg_create_address_file);

  try
  {
    if (spendkey)
    {
      m_wallet->generate(m_wallet_file, std::move(rc.second).password(), address, *spendkey, viewkey, create_address_file);
    }
    else
    {
      m_wallet->generate(m_wallet_file, std::move(rc.second).password(), address, viewkey, create_address_file);
    }
    message_writer(console_color_white, true) << tr("新钱包已生成：")
      << m_wallet->get_account().get_public_address_str(m_wallet->nettype());
  }
  catch (const std::exception& e)
  {
    fail_msg_writer() << tr("生成新钱包失败：") << e.what();
    return {};
  }


  return password;
}

//----------------------------------------------------------------------------------------------------
boost::optional<epee::wipeable_string> simple_wallet::new_wallet(const boost::program_options::variables_map& vm)
{
  std::pair<std::unique_ptr<tools::wallet2>, tools::password_container> rc;
  try { rc = tools::wallet2::make_new(vm, false, password_prompter); }
  catch(const std::exception &e) { fail_msg_writer() << tr("创建钱包失败：") << e.what(); return {}; }
  m_wallet = std::move(rc.first);
  if (!m_wallet)
  {
    return {};
  }
  m_wallet->callback(this);
  epee::wipeable_string password = rc.second.password();

  if (!m_subaddress_lookahead.empty())
  {
    auto lookahead = parse_subaddress_lookahead(m_subaddress_lookahead);
    assert(lookahead);
    m_wallet->set_subaddress_lookahead(lookahead->first, lookahead->second);
  }

  if (m_restore_height)
    m_wallet->set_refresh_from_block_height(m_restore_height);

  auto device_desc = tools::wallet2::device_name_option(vm);
  auto device_derivation_path = tools::wallet2::device_derivation_path_option(vm);
  try
  {
    bool create_address_file = command_line::get_arg(vm, arg_create_address_file);
    m_wallet->device_derivation_path(device_derivation_path);
    m_wallet->restore(m_wallet_file, std::move(rc.second).password(), device_desc.empty() ? "Ledger" : device_desc, create_address_file);
    message_writer(console_color_white, true) << tr("已在硬件设备上生成新钱包：")
      << m_wallet->get_account().get_public_address_str(m_wallet->nettype());
  }
  catch (const std::exception& e)
  {
    fail_msg_writer() << tr("生成新钱包失败：") << e.what();
    return {};
  }

  return password;
}
//----------------------------------------------------------------------------------------------------
boost::optional<epee::wipeable_string> simple_wallet::new_wallet(const boost::program_options::variables_map& vm,
    const epee::wipeable_string &multisig_keys, const epee::wipeable_string &seed_pass, const std::string &old_language)
{
  std::pair<std::unique_ptr<tools::wallet2>, tools::password_container> rc;
  try { rc = tools::wallet2::make_new(vm, false, password_prompter); }
  catch(const std::exception &e) { fail_msg_writer() << tr("创建钱包失败：") << e.what(); return {}; }
  m_wallet = std::move(rc.first);
  if (!m_wallet)
  {
    return {};
  }
  epee::wipeable_string password = rc.second.password();

  if (!m_subaddress_lookahead.empty())
  {
    auto lookahead = parse_subaddress_lookahead(m_subaddress_lookahead);
    assert(lookahead);
    m_wallet->set_subaddress_lookahead(lookahead->first, lookahead->second);
  }

  std::string mnemonic_language = old_language;

  std::vector<std::string> language_list;
  crypto::ElectrumWords::get_language_list(language_list);
  if (mnemonic_language.empty() && std::find(language_list.begin(), language_list.end(), m_mnemonic_language) != language_list.end())
  {
    mnemonic_language = m_mnemonic_language;
  }

  m_wallet->set_seed_language(mnemonic_language);

  bool create_address_file = command_line::get_arg(vm, arg_create_address_file);

  try
  {
    if (seed_pass.empty())
      m_wallet->generate(m_wallet_file, std::move(rc.second).password(), multisig_keys, create_address_file);
    else
    {
      crypto::secret_key key;
      crypto::cn_slow_hash(seed_pass.data(), seed_pass.size(), (crypto::hash&)key);
      sc_reduce32((unsigned char*)key.data);
      const epee::wipeable_string &msig_keys = m_wallet->decrypt<epee::wipeable_string>(std::string(multisig_keys.data(), multisig_keys.size()), key, true);
      m_wallet->generate(m_wallet_file, std::move(rc.second).password(), msig_keys, create_address_file);
    }
    const multisig::multisig_account_status ms_status{m_wallet->get_multisig_status()};

    if (!ms_status.multisig_is_active || !ms_status.is_ready)
    {
      fail_msg_writer() << tr("生成新的多重签名钱包失败");
      return {};
    }
    message_writer(console_color_white, true) << boost::format(tr("已生成新的 %u/%u 多重签名钱包：")) % ms_status.threshold % ms_status.total
      << m_wallet->get_account().get_public_address_str(m_wallet->nettype());
  }
  catch (const std::exception& e)
  {
    fail_msg_writer() << tr("生成新钱包失败：") << e.what();
    return {};
  }

  return password;
}
//----------------------------------------------------------------------------------------------------
boost::optional<epee::wipeable_string> simple_wallet::open_wallet(const boost::program_options::variables_map& vm)
{
  if (!tools::wallet2::wallet_valid_path_format(m_wallet_file))
  {
    fail_msg_writer() << tr("钱包文件路径无效：") << m_wallet_file;
    return {};
  }

  bool keys_file_exists;
  bool wallet_file_exists;

  tools::wallet2::wallet_exists(m_wallet_file, keys_file_exists, wallet_file_exists);
  if(!keys_file_exists)
  {
    fail_msg_writer() << tr("未找到密钥文件，打开钱包失败");
    return {};
  }
  
  epee::wipeable_string password;
  try
  {
    auto rc = tools::wallet2::make_from_file(vm, false, "", password_prompter);
    m_wallet = std::move(rc.first);
    password = std::move(std::move(rc.second).password());
    if (!m_wallet)
    {
      return {};
    }

    m_wallet->callback(this);
    m_wallet->load(m_wallet_file, password);
    std::string prefix;
    const multisig::multisig_account_status ms_status{m_wallet->get_multisig_status()};
    if (m_wallet->watch_only())
      prefix = tr("已打开仅观察钱包");
    else if (ms_status.multisig_is_active)
      prefix = (boost::format(tr("已打开 %u/%u 多重签名钱包%s")) % ms_status.threshold % ms_status.total % (ms_status.is_ready ? "" : " (not yet finalized)")).str();
    else if (m_wallet->is_background_wallet())
      prefix = tr("已打开后台钱包");
    else
      prefix = tr("已打开钱包");
    message_writer(console_color_white, true) <<
      prefix << ": " << m_wallet->get_account().get_public_address_str(m_wallet->nettype());
    if (m_wallet->get_account().get_device()) {
       message_writer(console_color_white, true) << "Wallet is on device: " << m_wallet->get_account().get_device().get_name();
    }
    // If the wallet file is deprecated, we should ask for mnemonic language again and store
    // everything in the new format.
    // NOTE: this is_deprecated() refers to the wallet file format before becoming JSON. It does not refer to the "old english" seed words form of "deprecated" used elsewhere.
    if (m_wallet->is_deprecated())
    {
      bool is_deterministic;
      {
        SCOPED_WALLET_UNLOCK_ON_BAD_PASSWORD(return {};);
        is_deterministic = m_wallet->is_deterministic();
      }
      if (is_deterministic)
      {
        message_writer(console_color_green, false) << "\n" << tr("You had been using "
          "a deprecated version of the wallet. Please proceed to upgrade your wallet.\n");
        std::string mnemonic_language = get_mnemonic_language(false);
        if (mnemonic_language.empty())
          return {};
        m_wallet->set_seed_language(mnemonic_language);
        m_wallet->rewrite(m_wallet_file, password);

        // Display the seed
        epee::wipeable_string seed;
        m_wallet->get_seed(seed);
        print_seed(seed, false, 0, false);
      }
      else
      {
        message_writer(console_color_green, false) << "\n" << tr("You had been using "
          "a deprecated version of the wallet. Your wallet file format is being upgraded now.\n");
        m_wallet->rewrite(m_wallet_file, password);
      }
    }

    if (!m_wallet->is_polyseed() && !ms_status.multisig_is_active)
    {
      std::string seed;
      bool has_feather_seed = m_wallet->get_attribute("feather.seed", seed);
      // We ignore the "feather.seedoffset" attribute as we, unlike Feather Wallet, don't store passphrases
      if (has_feather_seed)
      {
        polyseed::data polyseed(POLYSEED_MONERO);
        polyseed::language lang;
        bool is_valid_polyseed = false;
        try
        {
          lang = polyseed.decode(seed.c_str());
          is_valid_polyseed = true;
        }
        catch (const std::exception& e)
        {
        }
        if (is_valid_polyseed)
        {
          // As yet unmodified wallet file written by Feather Wallet app: Switch to Polyseed "in our way";
          // file stays compatible with Feather
          m_wallet->set_seed_language(lang.name());
          crypto::secret_key polyseed_storage;
          polyseed.save(&polyseed_storage);
          {
            tools::wallet_keys_unlocker unlocker(*m_wallet, &password);
            m_wallet->get_account().set_polyseed(polyseed_storage);
          }
          m_wallet->set_is_polyseed(true);
          m_wallet->rewrite(m_wallet_file, password);

        }
        memwipe(seed.data(), seed.size());
      }
    }
  }

  catch (const std::exception& e)
  {
    fail_msg_writer() << tr("加载钱包失败：") << e.what();
    if (m_wallet)
    {
      // only suggest removing cache if the password was actually correct
      bool password_is_correct = false;
      try
      {
        password_is_correct = m_wallet->verify_password(password);
      }
      catch (...) { } // guard against I/O errors
      if (password_is_correct)
        fail_msg_writer() << boost::format(tr("您可以删除文件“%s”后重试")) % m_wallet_file;
    }
    return {};
  }
  success_msg_writer() <<
    "**********************************************************************\n" <<
    tr("Use the \"help\" command to see a simplified list of available commands.\n") <<
    tr("Use \"help all\" to see the list of all available commands.\n") <<
    tr("Use \"help <command>\" to see a command's documentation.\n") <<
    "**********************************************************************";
  return password;
}
//----------------------------------------------------------------------------------------------------
bool simple_wallet::close_wallet()
{
  if (m_idle_run.load(std::memory_order_relaxed))
  {
    m_idle_run.store(false, std::memory_order_relaxed);
    m_wallet->stop();
    {
      boost::unique_lock<boost::mutex> lock(m_idle_mutex);
      m_idle_cond.notify_one();
    }
    m_idle_thread.join();
  }

  bool r = m_wallet->deinit();
  if (!r)
  {
    fail_msg_writer() << tr("卸载钱包失败");
    return false;
  }

  try
  {
    m_wallet->store();
  }
  catch (const std::exception& e)
  {
    fail_msg_writer() << e.what();
    return false;
  }

  return true;
}
//----------------------------------------------------------------------------------------------------
bool simple_wallet::save(const std::vector<std::string> &args)
{
  if (!m_wallet)
  {
    fail_msg_writer() << tr("钱包为空");
    return true;
  }

  try
  {
    LOCK_IDLE_SCOPE();
    m_wallet->store();
    success_msg_writer() << tr("钱包数据已保存");
  }
  catch (const std::exception& e)
  {
    fail_msg_writer() << e.what();
  }

  return true;
}
//----------------------------------------------------------------------------------------------------
bool simple_wallet::save_watch_only(const std::vector<std::string> &args/* = std::vector<std::string>()*/)
{
  if (!m_wallet)
  {
    fail_msg_writer() << tr("钱包为空");
    return true;
  }

  if (m_wallet->get_multisig_status().multisig_is_active)
  {
    fail_msg_writer() << tr("多重签名钱包无法保存为仅观察版本");
    return true;
  }

  const auto pwd_container = password_prompter(tr("新仅观察钱包的密码"), true);

  if (!pwd_container)
  {
    fail_msg_writer() << tr("读取钱包密码失败");
    return true;
  }

  try
  {
    std::string new_keys_filename;
    m_wallet->write_watch_only_wallet(m_wallet_file, pwd_container->password(), new_keys_filename);
    success_msg_writer() << tr("仅观察钱包已保存为：") << new_keys_filename;
  }
  catch (const std::exception &e)
  {
    fail_msg_writer() << tr("保存仅观察钱包失败：") << e.what();
    return true;
  }
  return true;
}
//----------------------------------------------------------------------------------------------------
void simple_wallet::start_background_mining()
{
  COMMAND_RPC_MINING_STATUS::request reqq;
  COMMAND_RPC_MINING_STATUS::response resq;
  bool r = m_wallet->invoke_http_json("/mining_status", reqq, resq);
  std::string err = interpret_rpc_response(r, resq.status);
  if (!r)
    return;
  if (!err.empty())
  {
    fail_msg_writer() << tr("查询挖矿状态失败：") << err;
    return;
  }
  if (!resq.is_background_mining_enabled)
  {
    COMMAND_RPC_START_MINING::request req;
    COMMAND_RPC_START_MINING::response res;
    req.miner_address = m_wallet->get_account().get_public_address_str(m_wallet->nettype());
    req.threads_count = 1;
    req.do_background_mining = true;
    req.ignore_battery = false;
    bool r = m_wallet->invoke_http_json("/start_mining", req, res);
    std::string err = interpret_rpc_response(r, res.status);
    if (!err.empty())
    {
      fail_msg_writer() << tr("设置后台挖矿失败：") << err;
      return;
    }
  }
  success_msg_writer() << tr("后台挖矿已启用。感谢您支持 Monero 网络。");
}
//----------------------------------------------------------------------------------------------------
void simple_wallet::stop_background_mining()
{
  COMMAND_RPC_MINING_STATUS::request reqq;
  COMMAND_RPC_MINING_STATUS::response resq;
  bool r = m_wallet->invoke_http_json("/mining_status", reqq, resq);
  if (!r)
    return;
  std::string err = interpret_rpc_response(r, resq.status);
  if (!err.empty())
  {
    fail_msg_writer() << tr("查询挖矿状态失败：") << err;
    return;
  }
  if (resq.is_background_mining_enabled)
  {
    COMMAND_RPC_STOP_MINING::request req;
    COMMAND_RPC_STOP_MINING::response res;
    bool r = m_wallet->invoke_http_json("/stop_mining", req, res);
    std::string err = interpret_rpc_response(r, res.status);
    if (!err.empty())
    {
      fail_msg_writer() << tr("设置后台挖矿失败：") << err;
      return;
    }
  }
  message_writer(console_color_red, false) << tr("后台挖矿未启用。运行“set setup-background-mining 1”可修改。");
}
//----------------------------------------------------------------------------------------------------
void simple_wallet::check_background_mining(const epee::wipeable_string &password)
{
  if (!m_wallet) return;

  // Background mining can be toggled from the main wallet
  if (m_wallet->is_background_wallet() || m_wallet->is_background_syncing())
    return;

  tools::wallet2::BackgroundMiningSetupType setup = m_wallet->setup_background_mining();
  if (setup == tools::wallet2::BackgroundMiningNo)
  {
    message_writer(console_color_red, false) << tr("后台挖矿未启用。运行“set setup-background-mining 1”可修改。");
    return;
  }

  if (!m_wallet->is_trusted_daemon())
  {
    message_writer() << tr("正在使用不受信任的守护进程，跳过后台挖矿检查");
    return;
  }

  COMMAND_RPC_MINING_STATUS::request req;
  COMMAND_RPC_MINING_STATUS::response res;
  bool r = m_wallet->invoke_http_json("/mining_status", req, res);
  std::string err = interpret_rpc_response(r, res.status);
  bool is_background_mining_enabled = false;
  if (err.empty())
    is_background_mining_enabled = res.is_background_mining_enabled;

  if (is_background_mining_enabled)
  {
    // already active, nice
    if (setup == tools::wallet2::BackgroundMiningMaybe)
    {
      m_wallet->setup_background_mining(tools::wallet2::BackgroundMiningYes);
      m_wallet->rewrite(m_wallet_file, password);
    }
    start_background_mining();
    return;
  }
  if (res.active)
    return;

  if (setup == tools::wallet2::BackgroundMiningMaybe)
  {
    message_writer() << tr("守护进程未设置后台挖矿。");
    message_writer() << tr("启用后台挖矿后，守护进程会在设备空闲且未使用电池时挖矿。");
    message_writer() << tr("启用此功能可以支持您正在使用的网络，并使您有机会获得新的 Monero");
    std::string accepted = input_line(tr("现在要启用吗？"), true);
    if (std::cin.eof() || !command_line::is_yes(accepted)) {
      m_wallet->setup_background_mining(tools::wallet2::BackgroundMiningNo);
      m_wallet->rewrite(m_wallet_file, password);
      message_writer(console_color_red, false) << tr("后台挖矿未启用。设置 setup-background-mining=1 以更改。");
      return;
    }
    m_wallet->setup_background_mining(tools::wallet2::BackgroundMiningYes);
    m_wallet->rewrite(m_wallet_file, password);
    start_background_mining();
  }
  else
  {
    // the setting is already enabled, and the daemon is not mining yet, so start it
    start_background_mining();
  }
}
//----------------------------------------------------------------------------------------------------
bool simple_wallet::start_mining(const std::vector<std::string>& args)
{
  if (!m_wallet)
  {
    fail_msg_writer() << tr("钱包为空");
    return true;
  }

  if (!m_wallet->is_trusted_daemon())
  {
    fail_msg_writer() << tr("此命令需要可信守护进程，请使用 --trusted-daemon 启用");
    return true;
  }

  if (!try_connect_to_daemon())
    return true;

  COMMAND_RPC_START_MINING::request req = AUTO_VAL_INIT(req); 
  req.miner_address = m_wallet->get_account().get_public_address_str(m_wallet->nettype());

  bool ok = true;
  size_t arg_size = args.size();
  if(arg_size >= 3)
  {
    if (!parse_bool_and_use(args[2], [&](bool r) { req.ignore_battery = r; }))
      return true;
  }
  if(arg_size >= 2)
  {
    if (!parse_bool_and_use(args[1], [&](bool r) { req.do_background_mining = r; }))
      return true;
  }
  if(arg_size >= 1)
  {
    uint16_t num = 1;
    ok = string_tools::get_xtype_from_string(num, args[0]);
    ok = ok && 1 <= num;
    req.threads_count = num;
  }
  else
  {
    req.threads_count = 1;
  }

  if (!ok)
  {
    PRINT_USAGE(USAGE_START_MINING);
    return true;
  }

  const unsigned int hw_concurrency = boost::thread::hardware_concurrency();
  if (hw_concurrency && req.threads_count > hw_concurrency)
  {
    message_writer(console_color_yellow, false) << boost::format(tr("警告：%u mining threads requested exceeds the %u hardware threads available on this CPU. Consider using %u for best performance.")) % req.threads_count % hw_concurrency % hw_concurrency;
  }

  COMMAND_RPC_START_MINING::response res;
  bool r = m_wallet->invoke_http_json("/start_mining", req, res);
  std::string err = interpret_rpc_response(r, res.status);
  if (err.empty())
    success_msg_writer() << tr("已在守护进程中开始挖矿");
  else
    fail_msg_writer() << tr("尚未开始挖矿：") << err;
  return true;
}
//----------------------------------------------------------------------------------------------------
bool simple_wallet::stop_mining(const std::vector<std::string>& args)
{
  if (!try_connect_to_daemon())
    return true;

  if (!m_wallet)
  {
    fail_msg_writer() << tr("钱包为空");
    return true;
  }

  COMMAND_RPC_STOP_MINING::request req;
  COMMAND_RPC_STOP_MINING::response res;
  bool r = m_wallet->invoke_http_json("/stop_mining", req, res);
  std::string err = interpret_rpc_response(r, res.status);
  if (err.empty())
    success_msg_writer() << tr("已在守护进程中停止挖矿");
  else
    fail_msg_writer() << tr("尚未停止挖矿：") << err;
  return true;
}
//----------------------------------------------------------------------------------------------------
bool simple_wallet::set_daemon(const std::vector<std::string>& args)
{
  std::string daemon_url;

  if (args.size() < 1)
  {
    PRINT_USAGE(USAGE_SET_DAEMON);
    return true;
  }

  boost::regex rgx("^(.*://)?([A-Za-z0-9\\-\\.]+)(:[0-9]+)?");
  boost::cmatch match;
  // If user input matches URL regex
  if (boost::regex_match(args[0].c_str(), match, rgx))
  {
    if (match.length() < 4)
    {
      fail_msg_writer() << tr("数组长度异常——已退出 simple_wallet::set_daemon()");
      return true;
    }
    // If no port has been provided, use the default from config
    if (!match[3].length())
    {
      uint16_t daemon_port = get_config(m_wallet->nettype()).RPC_DEFAULT_PORT;
      daemon_url = match[1] + match[2] + std::string(":") + std::to_string(daemon_port);
    } else {
      daemon_url = args[0];
    }

    epee::net_utils::http::url_content parsed{};
    const bool r = epee::net_utils::parse_url(daemon_url, parsed);
    if (!r)
    {
      fail_msg_writer() << tr("解析地址失败");
      return true;
    }

    std::string trusted;
    if (args.size() == 2)
    {
      if (args[1] == "trusted")
        trusted = "trusted";
      else if (args[1] == "untrusted")
        trusted = "untrusted";
      else if (args[1] == "this-is-probably-a-spy-node")
        trusted = "this-is-probably-a-spy-node";
      else
      {
        fail_msg_writer() << tr("期望 trusted、untrusted 或 this-is-probably-a-spy-node，但实际得到 ") << args[1];
        return true;
      }
    }

    if (!tools::is_privacy_preserving_network(parsed.host) && !tools::is_local_address(parsed.host))
    {
      if (trusted == "untrusted" || trusted == "")
      {
        fail_msg_writer() << tr("这不是 Tor/I2P 地址，也不是受信任的守护进程。");
        fail_msg_writer() << tr("请使用您自己的受信任节点，通过 Tor 或 I2P 连接，或传入 this-is-probably-a-spy-node 并接受可能被监视的风险。");
        return true;
      }

      if (parsed.schema != "https")
        message_writer(console_color_red) << tr("警告：connecting to a non-local daemon without SSL, passive adversaries will be able to spy on you.");
    }

    LOCK_IDLE_SCOPE();
    m_wallet->init(daemon_url);

    if (!trusted.empty())
    {
      m_wallet->set_trusted_daemon(trusted == "trusted");
    }
    else
    {
      m_wallet->set_trusted_daemon(false);
      try
      {
        if (tools::is_local_address(m_wallet->get_daemon_address()))
        {
          MINFO(tr("守护进程位于本地，默认视为可信"));
          m_wallet->set_trusted_daemon(true);
        }
      }
      catch (const std::exception &e) { }
    }

    if (!try_connect_to_daemon())
    {
      fail_msg_writer() << tr("连接守护进程失败");
      return true;
    }

    success_msg_writer() << boost::format("守护进程已设置为 %s，%s") % daemon_url % (m_wallet->is_trusted_daemon() ? tr("受信任") : tr("un受信任"));
  } else {
    fail_msg_writer() << tr("这似乎不是有效的守护进程地址。");
  }
  return true;
}
//----------------------------------------------------------------------------------------------------
bool simple_wallet::save_bc(const std::vector<std::string>& args)
{
  if (!try_connect_to_daemon())
    return true;

  if (!m_wallet)
  {
    fail_msg_writer() << tr("钱包为空");
    return true;
  }
  COMMAND_RPC_SAVE_BC::request req;
  COMMAND_RPC_SAVE_BC::response res;
  bool r = m_wallet->invoke_http_json("/save_bc", req, res);
  std::string err = interpret_rpc_response(r, res.status);
  if (err.empty())
    success_msg_writer() << tr("区块链数据已保存");
  else
    fail_msg_writer() << tr("区块链数据无法保存：") << err;
  return true;
}
//----------------------------------------------------------------------------------------------------
void simple_wallet::on_new_block(uint64_t height, const cryptonote::block& block)
{
  if (m_locked)
    return;
  if (!m_auto_refresh_refreshing)
    m_refresh_progress_reporter.update(height, false);
}
//----------------------------------------------------------------------------------------------------
void simple_wallet::on_money_received(uint64_t height, const crypto::hash &txid,
  const cryptonote::transaction& tx, uint64_t amount, uint64_t burnt,
  const cryptonote::subaddress_index& subaddr_index, const crypto::hash &payment_id, bool is_change,
  uint64_t unlock_time)
{
  if (m_locked)
    return;
  std::stringstream burn;
  if (burnt != 0) {
    burn << " (" << print_money(amount) << " yet " << print_money(burnt) << " was burnt)";
  }
  message_writer(console_color_green, false) << "\r" <<
    tr("高度 ") << height << ", " <<
    tr("txid ") << txid << ", " <<
    print_money(amount - burnt) << burn.str() << ", " <<
    tr("idx ") << subaddr_index;

  const uint64_t warn_height = m_wallet->nettype() == TESTNET ? 1000000 : m_wallet->nettype() == STAGENET ? 50000 : 1650000;
  if (height >= warn_height && !is_change)
  {
    std::vector<tx_extra_field> tx_extra_fields;
    parse_tx_extra(tx.extra, tx_extra_fields); // failure ok
    tx_extra_nonce extra_nonce;
    crypto::hash8 payment_id8 = crypto::null_hash8;
    {
      if (find_tx_extra_field_by_type(tx_extra_fields, extra_nonce))
      {
        if (get_encrypted_payment_id_from_tx_extra_nonce(extra_nonce.nonce, payment_id8))
        {
          memcpy(payment_id8.data, payment_id.data, sizeof(payment_id8));
        }
     }
    }

    if (payment_id8 != crypto::null_hash8)
      message_writer() <<
        tr("注意：此交易使用加密支付 ID，建议改用子地址。");

    crypto::hash payment_id = crypto::null_hash;
    if (get_payment_id_from_tx_extra_nonce(extra_nonce.nonce, payment_id))
      message_writer(console_color_red, false) <<
        tr("警告：此交易使用未加密的支付 ID；此功能已废弃并会被忽略。请改用子地址。");
  }
  if (unlock_time && !tx.is_coinbase())
    message_writer() << tr("注意：此交易已锁定，请使用 show_transfer 查看详情。") + epee::string_tools::pod_to_hex(txid);
  if (m_auto_refresh_refreshing)
    m_cmd_binder.print_prompt();
  else
    m_refresh_progress_reporter.update(height, true);
}
//----------------------------------------------------------------------------------------------------
void simple_wallet::on_unconfirmed_money_received(uint64_t height, const crypto::hash &txid, const cryptonote::transaction& tx, uint64_t amount, const cryptonote::subaddress_index& subaddr_index)
{
  if (m_locked)
    return;
  // Not implemented in CLI wallet
}
//----------------------------------------------------------------------------------------------------
void simple_wallet::on_money_spent(uint64_t height, const crypto::hash &txid, const cryptonote::transaction& in_tx, uint64_t amount, const cryptonote::transaction& spend_tx, const cryptonote::subaddress_index& subaddr_index)
{
  if (m_locked)
    return;
  message_writer(console_color_magenta, false) << "\r" <<
    tr("高度 ") << height << ", " <<
    tr("txid ") << txid << ", " <<
    tr("spent ") << print_money(amount) << ", " <<
    tr("idx ") << subaddr_index;
  if (m_auto_refresh_refreshing)
    m_cmd_binder.print_prompt();
  else
    m_refresh_progress_reporter.update(height, true);
}
//----------------------------------------------------------------------------------------------------
void simple_wallet::on_skip_transaction(uint64_t height, const crypto::hash &txid, const cryptonote::transaction& tx)
{
  if (m_locked)
    return;
}
//----------------------------------------------------------------------------------------------------
boost::optional<epee::wipeable_string> simple_wallet::on_get_password(const char *reason)
{
  if (m_locked)
    return boost::none;
  // can't ask for password from a background thread
  if (!m_in_manual_refresh.load(std::memory_order_relaxed))
  {
    message_writer(console_color_red, false) << boost::format(tr("需要密码（%s），请使用 refresh 命令")) % reason;
    m_cmd_binder.print_prompt();
    return boost::none;
  }

  PAUSE_READLINE();
  std::string msg = tr("请输入密码");
  if (reason && *reason)
    msg += std::string(" (") + reason + ")";
  auto pwd_container = tools::password_container::prompt(false, msg.c_str());
  if (!pwd_container)
  {
    MERROR("Failed to read password");
    return boost::none;
  }

  return pwd_container->password();
}
//----------------------------------------------------------------------------------------------------
void simple_wallet::on_device_button_request(uint64_t code)
{
  message_writer(console_color_white, false) << tr("设备请求确认");
}
//----------------------------------------------------------------------------------------------------
boost::optional<epee::wipeable_string> simple_wallet::on_device_pin_request()
{
  PAUSE_READLINE();
  std::string msg = tr("请输入设备 PIN");
  auto pwd_container = tools::password_container::prompt(false, msg.c_str());
  THROW_WALLET_EXCEPTION_IF(!pwd_container, tools::error::password_entry_failed, tr("读取设备 PIN 失败"));
  return pwd_container->password();
}
//----------------------------------------------------------------------------------------------------
boost::optional<epee::wipeable_string> simple_wallet::on_device_passphrase_request(bool & on_device)
{
  if (on_device) {
    std::string accepted = input_line(tr(
        "Device asks for passphrase. Do you want to enter the passphrase on device (Y) (or on the host (N))?"));
    if (std::cin.eof() || command_line::is_yes(accepted)) {
      message_writer(console_color_white, true) << tr("请在设备上输入设备密码短语");
      return boost::none;
    }
  }

  PAUSE_READLINE();
  on_device = false;
  std::string msg = tr("请输入设备密码短语");
  auto pwd_container = tools::password_container::prompt(false, msg.c_str());
  THROW_WALLET_EXCEPTION_IF(!pwd_container, tools::error::password_entry_failed, tr("读取设备密码短语失败"));
  return pwd_container->password();
}
//----------------------------------------------------------------------------------------------------
void simple_wallet::on_refresh_finished(uint64_t start_height, uint64_t fetched_blocks, bool is_init, bool received_money)
{
  const uint64_t rfbh = m_wallet->get_refresh_from_block_height();
  std::string err;
  const uint64_t dh = m_wallet->get_daemon_blockchain_height(err);
  if (err.empty() && rfbh > dh)
  {
    message_writer(console_color_yellow, false) << tr("钱包的刷新起始区块高度高于守护进程当前高度，这可能导致钱包跳过部分交易");
  }

  // Key image sync after the first refresh
  if (!m_wallet->get_account().get_device().has_tx_cold_sign() || m_wallet->get_account().get_device().has_ki_live_refresh()) {
    return;
  }

  if (!received_money || m_wallet->get_device_last_key_image_sync() != 0) {
    return;
  }

  // Finished first refresh for HW device and money received -> KI sync
  message_writer() << "\n" << tr("基于硬件钱包的首次刷新已完成，但收到的资金仍需要执行 hw_key_images_sync。");

  std::string accepted = input_line(tr("现在要启用吗？"), true);
  if (std::cin.eof() || !command_line::is_yes(accepted)) {
    message_writer(console_color_red, false) << tr("已跳过 hw_key_images_sync。转账前请手动执行该命令。");
    return;
  }

  key_images_sync_intern();
}
//----------------------------------------------------------------------------------------------------
bool simple_wallet::refresh_main(uint64_t start_height, enum ResetType reset, bool is_init)
{
  if (!try_connect_to_daemon(is_init))
    return true;

  LOCK_IDLE_SCOPE();

  crypto::hash transfer_hash_pre{};
  uint64_t height_pre = 0, height_post;
  if (reset != ResetNone)
  {
    if (reset == ResetSoftKeepKI)
      height_pre = m_wallet->hash_m_transfers(boost::none, transfer_hash_pre);

    m_wallet->rescan_blockchain(reset == ResetHard, false, reset == ResetSoftKeepKI);
  }

  PAUSE_READLINE();

  message_writer() << tr("正在开始同步……");

  uint64_t fetched_blocks = 0;
  bool received_money = false;
  bool ok = false;
  bool suggest_hw_reconnect = false;
  std::ostringstream ss;
  try
  {
    m_in_manual_refresh.store(true, std::memory_order_relaxed);
    const epee::scope_guard scope_exit_handler([&](){m_in_manual_refresh.store(false, std::memory_order_relaxed);});
    // For manual refresh don't allow incremental checking of the pool: Because we did not process the txs
    // for us in the pool during automatic refresh we could miss some of them if we checked the pool
    // incrementally here
    m_wallet->refresh(m_wallet->is_trusted_daemon(), start_height, fetched_blocks, received_money, true, false);

    if (reset == ResetSoftKeepKI)
    {
      m_wallet->finish_rescan_bc_keep_key_images(height_pre, transfer_hash_pre);

      height_post = m_wallet->get_num_transfer_details();
      if (height_pre != height_post)
      {
        message_writer() << tr("重新扫描开始后收到新的转账，密钥镜像尚不完整。");
      }
    }

    ok = true;
    // Clear line "Height xxx of xxx"
    std::cout << "\r                                                                \r";
    success_msg_writer(true) << tr("同步完成，接收区块数：") << fetched_blocks;
    if (is_init)
      print_accounts();
    show_balance_unlocked();
    on_refresh_finished(start_height, fetched_blocks, is_init, received_money);
  }
  catch (const tools::error::daemon_busy&)
  {
    ss << tr("守护进程正忙，请稍后再试。");
  }
  catch (const tools::error::no_connection_to_daemon&)
  {
    ss << tr("无法连接到守护进程，请确认守护进程正在运行。");
  }
  catch (const tools::error::deprecated_rpc_access&)
  {
    ss << tr("守护进程要求使用已废弃的 RPC 支付方式。参见 https://github.com/monero-project/monero/issues/8722");
  }
  catch (const tools::error::wallet_rpc_error& e)
  {
    LOG_ERROR("RPC 错误：" << e.to_string());
    ss << tr("RPC 错误：") << e.what();
  }
  catch (const tools::error::refresh_error& e)
  {
    LOG_ERROR("同步错误：" << e.to_string());
    ss << tr("同步错误：") << e.what();
  }
  catch (const tools::error::wallet_internal_error& e)
  {
    LOG_ERROR("内部错误：" << e.to_string());
    ss << tr("内部错误：") << e.what();
  }
  catch (const std::exception& e)
  {
    LOG_ERROR("意外错误：" << e.what());
    ss << tr("意外错误：") << e.what();
    suggest_hw_reconnect = true;
  }
  catch (...)
  {
    LOG_ERROR("未知错误");
    ss << tr("未知错误");
  }

  if (!ok)
  {
    auto writer = fail_msg_writer();
    writer << tr("同步失败：") << ss.str() << ". " << tr("已接收区块数：") << fetched_blocks;
    if (suggest_hw_reconnect && m_wallet->key_on_device())
      writer << "\n" << tr("请确认硬件钱包已连接并解锁，然后执行 'hw_reconnect'，再重新刷新。");
  }

  // prevent it from triggering the idle screen due to waiting for a foreground refresh
  m_last_activity_time = time(NULL);

  return true;
}
//----------------------------------------------------------------------------------------------------
bool simple_wallet::refresh(const std::vector<std::string>& args)
{
  uint64_t start_height = 0;
  if(!args.empty()){
    try
    {
        start_height = boost::lexical_cast<uint64_t>( args[0] );
    }
    catch(const boost::bad_lexical_cast &)
    {
        start_height = 0;
    }
  }
  return refresh_main(start_height, ResetNone);
}
//----------------------------------------------------------------------------------------------------
bool simple_wallet::show_balance_unlocked(bool detailed)
{
  std::string extra;
  if (m_wallet->has_multisig_partial_key_images())
    extra = tr("（部分属于您的输出只有不完整的密钥镜像，需要执行 import_multisig_info。）");
  else if (m_wallet->has_unknown_key_images())
    extra += tr("（部分属于您的输出缺少密钥镜像，需要执行 export_outputs、import_outputs、export_key_images 和 import_key_images。）");
  success_msg_writer() << tr("当前选中账户：[") << m_current_subaddress_account << tr("] ") << m_wallet->get_subaddress_label({m_current_subaddress_account, 0});
  const std::string tag = m_wallet->get_account_tags().second[m_current_subaddress_account];
  success_msg_writer() << tr("标签：") << (tag.empty() ? std::string{tr("（未分配标签）")} : tag);
  uint64_t blocks_to_unlock, time_to_unlock;
  uint64_t unlocked_balance = m_wallet->unlocked_balance(m_current_subaddress_account, false, &blocks_to_unlock, &time_to_unlock);
  std::string unlock_time_message;
  if (blocks_to_unlock > 0 && time_to_unlock > 0)
    unlock_time_message = (boost::format(" (%lu block(s) and %s to unlock)") % blocks_to_unlock % tools::get_human_readable_timespan(time_to_unlock)).str();
  else if (blocks_to_unlock > 0)
    unlock_time_message = (boost::format(" (%lu block(s) to unlock)") % blocks_to_unlock).str();
  else if (time_to_unlock > 0)
    unlock_time_message = (boost::format(" (%s to unlock)") % tools::get_human_readable_timespan(time_to_unlock)).str();
  success_msg_writer() << tr("余额：") << print_money(m_wallet->balance(m_current_subaddress_account, false)) << ", "
    << tr("可用余额：") << print_money(unlocked_balance) << unlock_time_message << extra;
  std::map<uint32_t, uint64_t> balance_per_subaddress = m_wallet->balance_per_subaddress(m_current_subaddress_account, false);
  std::map<uint32_t, std::pair<uint64_t, std::pair<uint64_t, uint64_t>>> unlocked_balance_per_subaddress = m_wallet->unlocked_balance_per_subaddress(m_current_subaddress_account, false);
  if (!detailed || balance_per_subaddress.empty())
    return true;
  success_msg_writer() << tr("按地址显示余额：");
  success_msg_writer() << boost::format("%15s %21s %21s %7s %21s") % tr("Address") % tr("余额") % tr("可用余额") % tr("输出") % tr("标签");
  std::vector<tools::wallet2::transfer_details> transfers;
  m_wallet->get_transfers(transfers);
  for (const auto& i : balance_per_subaddress)
  {
    cryptonote::subaddress_index subaddr_index = {m_current_subaddress_account, i.first};
    std::string address_str = m_wallet->get_subaddress_as_str(subaddr_index).substr(0, 6);
    uint64_t num_unspent_outputs = std::count_if(transfers.begin(), transfers.end(), [&subaddr_index](const tools::wallet2::transfer_details& td) { return !td.m_spent && td.m_subaddr_index == subaddr_index; });
    success_msg_writer() << boost::format(tr("%8u %6s %21s %21s %7u %21s")) % i.first % address_str % print_money(i.second) % print_money(unlocked_balance_per_subaddress[i.first].first) % num_unspent_outputs % m_wallet->get_subaddress_label(subaddr_index);
  }
  return true;
}
//----------------------------------------------------------------------------------------------------
bool simple_wallet::show_balance(const std::vector<std::string>& args/* = std::vector<std::string>()*/)
{
  if (args.size() > 1 || (args.size() == 1 && args[0] != "detail"))
  {
    PRINT_USAGE(USAGE_SHOW_BALANCE);
    return true;
  }
  LOCK_IDLE_SCOPE();
  show_balance_unlocked(args.size() == 1);
  return true;
}
//----------------------------------------------------------------------------------------------------
bool simple_wallet::show_incoming_transfers(const std::vector<std::string>& args)
{
  if (args.size() > 3)
  {
    PRINT_USAGE(USAGE_INCOMING_TRANSFERS);
    return true;
  }
  auto local_args = args;
  LOCK_IDLE_SCOPE();

  std::set<uint32_t> subaddr_indices;
  bool filter = false;
  bool available = false;
  bool verbose = false;
  bool uses = false;
  if (local_args.size() > 0)
  {
    if (local_args[0] == "available")
    {
      filter = true;
      available = true;
      local_args.erase(local_args.begin());
    }
    else if (local_args[0] == "unavailable")
    {
      filter = true;
      available = false;
      local_args.erase(local_args.begin());
    }
  }
  while (local_args.size() > 0)
  {
    if (local_args[0] == "verbose")
      verbose = true;
    else if (local_args[0] == "uses")
      uses = true;
    else if (local_args[0].substr(0, 6) == "index=")
    {
      if (!parse_subaddress_indices(local_args[0], subaddr_indices))
        return true;
    }
    else
    {
      fail_msg_writer() << tr("无效关键词：") << local_args.front();
      break;
    }
    local_args.erase(local_args.begin());
  }

  const uint64_t blockchain_height = m_wallet->get_blockchain_current_height();

  PAUSE_READLINE();

  if (local_args.size() > 0)
  {
    PRINT_USAGE(USAGE_INCOMING_TRANSFERS);
    return true;
  }

  tools::wallet2::transfer_container transfers;
  m_wallet->get_transfers(transfers);

  size_t transfers_found = 0;
  for (const auto& td : transfers)
  {
    if (!filter || available != td.m_spent)
    {
      if (m_current_subaddress_account != td.m_subaddr_index.major || (!subaddr_indices.empty() && subaddr_indices.count(td.m_subaddr_index.minor) == 0))
        continue;
      if (!transfers_found)
      {
        std::string verbose_string;
        if (verbose)
          verbose_string = (boost::format("%68s%68s") % tr("公钥") % tr("密钥镜像")).str();
        message_writer() << boost::format("%21s%8s%12s%8s%16s%68s%16s%s") % tr("amount") % tr("spent") % tr("unlocked") % tr("ringct") % tr("全局索引") % tr("tx id") % tr("地址索引") % verbose_string;
      }
      std::string extra_string;
      if (verbose)
        extra_string += (boost::format("%68s%68s") % td.get_public_key() % (td.m_key_image_known ? epee::string_tools::pod_to_hex(td.m_key_image) : td.m_key_image_partial ? (epee::string_tools::pod_to_hex(td.m_key_image) + "/p") : std::string(64, '?'))).str();
      if (uses)
      {
        std::vector<uint64_t> heights;
        uint64_t idx = 0;
        for (const auto &e: td.m_uses)
        {
          heights.push_back(e.first);
          if (e.first < td.m_spent_height)
            ++idx;
        }
        const std::pair<std::string, std::string> line = show_outputs_line(heights, blockchain_height, idx);
        extra_string += std::string("\n    ") + tr("使用于区块高度：") + line.first + "\n    " + line.second;
      }
      message_writer(td.m_spent ? console_color_magenta : console_color_green, false) <<
        boost::format("%21s%8s%12s%8s%16u%68s%16u%s") %
        print_money(td.amount()) %
        (td.m_spent ? tr("T") : tr("F")) %
        (m_wallet->frozen(td) ? tr("[frozen]") : m_wallet->is_transfer_unlocked(td) ? tr("unlocked") : tr("已锁定")) %
        (td.is_rct() ? tr("RingCT") : tr("-")) %
        td.m_global_output_index %
        td.m_txid %
        td.m_subaddr_index.minor %
        extra_string;
      ++transfers_found;
    }
  }

  if (!transfers_found)
  {
    if (!filter)
    {
      success_msg_writer() << tr("没有收到转账");
    }
    else if (available)
    {
      success_msg_writer() << tr("没有可用的入账转账");
    }
    else
    {
      success_msg_writer() << tr("没有不可用的入账转账");
    }
  }
  else
  {
    success_msg_writer() << boost::format("Found %u/%u transfers") % transfers_found % transfers.size();
  }

  return true;
}
//----------------------------------------------------------------------------------------------------
bool simple_wallet::show_payments(const std::vector<std::string> &args)
{
  if(args.empty())
  {
    PRINT_USAGE(USAGE_PAYMENTS);
    return true;
  }

  LOCK_IDLE_SCOPE();

  PAUSE_READLINE();

  message_writer() << boost::format("%68s%68s%12s%21s%16s%16s") %
    tr("payment") % tr("transaction") % tr("height") % tr("amount") % tr("unlock time") % tr("地址索引");

  bool payments_found = false;
  for(std::string arg : args)
  {
    crypto::hash payment_id;
    if(tools::wallet2::parse_payment_id(arg, payment_id))
    {
      std::list<tools::wallet2::payment_details> payments;
      m_wallet->get_payments(payment_id, payments);
      if(payments.empty())
      {
        success_msg_writer() << tr("没有支付 ID 为此值的支付：") << payment_id;
        continue;
      }

      for (const tools::wallet2::payment_details& pd : payments)
      {
        if(!payments_found)
        {
          payments_found = true;
        }
        success_msg_writer(true) <<
          boost::format("%68s%68s%12s%21s%16s%16s") %
          payment_id %
          pd.m_tx_hash %
          pd.m_block_height %
          print_money(pd.m_amount) %
          pd.m_unlock_time %
          pd.m_subaddr_index.minor;
      }
    }
    else
    {
      fail_msg_writer() << tr("付款 ID 格式无效，应为 16 或 64 个十六进制字符：") << arg;
    }
  }

  return true;
}
//----------------------------------------------------------------------------------------------------
uint64_t simple_wallet::get_daemon_blockchain_height(std::string& err)
{
  if (!m_wallet)
  {
    throw std::runtime_error("simple_wallet null wallet");
  }
  return m_wallet->get_daemon_blockchain_height(err);
}
//----------------------------------------------------------------------------------------------------
bool simple_wallet::show_blockchain_height(const std::vector<std::string>& args)
{
  if (!try_connect_to_daemon())
    return true;

  std::string err;
  uint64_t bc_height = get_daemon_blockchain_height(err);
  if (err.empty())
    success_msg_writer() << bc_height;
  else
    fail_msg_writer() << tr("获取区块链高度失败：") << err;
  return true;
}
//----------------------------------------------------------------------------------------------------
bool simple_wallet::rescan_spent(const std::vector<std::string> &args)
{
  CHECK_IF_BACKGROUND_SYNCING("cannot rescan spent");
  if (!m_wallet->is_trusted_daemon())
  {
    fail_msg_writer() << tr("此命令需要可信守护进程，请使用 --trusted-daemon 启用");
    return true;
  }

  if (!try_connect_to_daemon())
    return true;

  try
  {
    LOCK_IDLE_SCOPE();
    m_wallet->rescan_spent();
  }
  catch (const tools::error::daemon_busy&)
  {
    fail_msg_writer() << tr("守护进程正忙，请稍后再试。");
  }
  catch (const tools::error::no_connection_to_daemon&)
  {
    fail_msg_writer() << tr("无法连接到守护进程，请确认守护进程正在运行。");
  }
  catch (const tools::error::deprecated_rpc_access&)
  {
    fail_msg_writer() << tr("守护进程要求使用已废弃的 RPC 支付方式。参见 https://github.com/monero-project/monero/issues/8722");
  }
  catch (const tools::error::is_key_image_spent_error&)
  {
    fail_msg_writer() << tr("获取花费状态失败");
  }
  catch (const tools::error::wallet_rpc_error& e)
  {
    LOG_ERROR("RPC 错误：" << e.to_string());
    fail_msg_writer() << tr("RPC 错误：") << e.what();
  }
  catch (const std::exception& e)
  {
    LOG_ERROR("意外错误：" << e.what());
    fail_msg_writer() << tr("意外错误：") << e.what();
  }
  catch (...)
  {
    LOG_ERROR("未知错误");
    fail_msg_writer() << tr("未知错误");
  }

  return true;
}
//----------------------------------------------------------------------------------------------------
std::pair<std::string, std::string> simple_wallet::show_outputs_line(const std::vector<uint64_t> &heights, uint64_t blockchain_height, uint64_t highlight_idx) const
{
  std::stringstream ostr;

  for (uint64_t h: heights)
    blockchain_height = std::max(blockchain_height, h);

  for (size_t j = 0; j < heights.size(); ++j)
    ostr << (j == highlight_idx ? " *" : " ") << heights[j];

  // visualize the distribution, using the code by moneroexamples onion-monero-viewer
  const uint64_t resolution = 79;
  std::string ring_str(resolution, '_');
  for (size_t j = 0; j < heights.size(); ++j)
  {
    uint64_t pos = (heights[j] * resolution) / blockchain_height;
    ring_str[pos] = 'o';
  }
  if (highlight_idx < heights.size() && heights[highlight_idx] < blockchain_height)
  {
    uint64_t pos = (heights[highlight_idx] * resolution) / blockchain_height;
    ring_str[pos] = '*';
  }

  return std::make_pair(ostr.str(), ring_str);
}
//----------------------------------------------------------------------------------------------------
bool simple_wallet::process_ring_members(const std::vector<tools::wallet2::pending_tx>& ptx_vector, std::ostream& ostr, bool verbose)
{
  uint32_t version;
  if (!try_connect_to_daemon(false, &version))
  {
    fail_msg_writer() << tr("连接守护进程失败");
    return false;
  }
  // available for RPC version 1.4 or higher
  if (version < MAKE_CORE_RPC_VERSION(1, 4))
    return true;
  std::string err;
  uint64_t blockchain_height = get_daemon_blockchain_height(err);
  if (!err.empty())
  {
    fail_msg_writer() << tr("获取区块链高度失败：") << err;
    return false;
  }
  // for each transaction
  for (size_t n = 0; n < ptx_vector.size(); ++n)
  {
    const cryptonote::transaction& tx = ptx_vector[n].tx;
    const tools::wallet2::tx_construction_data& construction_data = ptx_vector[n].construction_data;
    if (verbose)
      ostr << boost::format(tr("\nTransaction %llu/%llu: txid=%s")) % (n + 1) % ptx_vector.size() % cryptonote::get_transaction_hash(tx);
    // for each input
    std::vector<uint64_t>     spent_key_height(tx.vin.size());
    std::vector<crypto::hash> spent_key_txid  (tx.vin.size());
    for (size_t i = 0; i < tx.vin.size(); ++i)
    {
      if (tx.vin[i].type() != typeid(cryptonote::txin_to_key))
        continue;
      const cryptonote::txin_to_key& in_key = boost::get<cryptonote::txin_to_key>(tx.vin[i]);
      const tools::wallet2::transfer_details &td = m_wallet->get_transfer_details(construction_data.selected_transfers[i]);
      const cryptonote::tx_source_entry *sptr = NULL;
      for (const auto &src: construction_data.sources)
        if (src.outputs[src.real_output].second.dest == td.get_public_key())
          sptr = &src;
      if (!sptr)
      {
        fail_msg_writer() << tr("未找到交易输入的构造数据");
        return false;
      }
      const cryptonote::tx_source_entry& source = *sptr;

      if (verbose)
        ostr << boost::format(tr("\nInput %llu/%llu (%s): amount=%s")) % (i + 1) % tx.vin.size() % epee::string_tools::pod_to_hex(in_key.k_image) % print_money(source.amount);
      // convert relative offsets of ring member keys into absolute offsets (indices) associated with the amount
      std::vector<uint64_t> absolute_offsets = cryptonote::relative_output_offsets_to_absolute(in_key.key_offsets);
      // get block heights from which those ring member keys originated
      COMMAND_RPC_GET_OUTPUTS_BIN::request req = AUTO_VAL_INIT(req);
      req.outputs.resize(absolute_offsets.size());
      for (size_t j = 0; j < absolute_offsets.size(); ++j)
      {
        req.outputs[j].amount = in_key.amount;
        req.outputs[j].index = absolute_offsets[j];
      }
      COMMAND_RPC_GET_OUTPUTS_BIN::response res = AUTO_VAL_INIT(res);
      req.get_txid = true;
      bool r = m_wallet->invoke_http_bin("/get_outs.bin", req, res);
      err = interpret_rpc_response(r, res.status);
      if (!err.empty())
      {
        fail_msg_writer() << tr("获取输出失败：") << err;
        return false;
      }
      if (res.outs.size() != req.outputs.size())
      {
        fail_msg_writer() << tr("守护进程返回了无效的输出数量");
        return false;
      }
      // make sure that returned block heights are less than blockchain height
      for (auto& res_out : res.outs)
      {
        if (res_out.height >= blockchain_height)
        {
          fail_msg_writer() << tr("输出密钥的来源区块高度不应高于当前区块链高度");
          return false;
        }
      }
      if (verbose)
        ostr << tr("\nOriginating block heights: ");
      spent_key_height[i] = res.outs[source.real_output].height;
      spent_key_txid  [i] = res.outs[source.real_output].txid;
      std::vector<uint64_t> heights(absolute_offsets.size(), 0);
      for (size_t j = 0; j < absolute_offsets.size(); ++j)
      {
        heights[j] = res.outs[j].height;
      }
      std::pair<std::string, std::string> ring_str = show_outputs_line(heights, blockchain_height, source.real_output);
      if (verbose)
        ostr << ring_str.first << tr("\n|") << ring_str.second << tr("|\n");
    }
    // warn if rings contain keys originating from the same tx or temporally very close block heights
    bool are_keys_from_same_tx      = false;
    bool are_keys_from_close_height = false;
    for (size_t i = 0; i < tx.vin.size(); ++i) {
      for (size_t j = i + 1; j < tx.vin.size(); ++j)
      {
        if (spent_key_txid[i] == spent_key_txid[j])
          are_keys_from_same_tx = true;
        if (std::abs((int64_t)(spent_key_height[i] - spent_key_height[j])) < (int64_t)5)
          are_keys_from_close_height = true;
      }
    }
    if (are_keys_from_same_tx || are_keys_from_close_height)
    {
      ostr
        << tr("\n警告：Some input keys being spent are from ")
        << (are_keys_from_same_tx ? tr("同一笔交易") : tr("时间上非常接近的区块"))
        << tr("，这可能破坏环签名的匿名性。请确认这是有意的！");
    }
    ostr << ENDL;
  }
  return true;
}
//----------------------------------------------------------------------------------------------------
bool simple_wallet::prompt_if_old(const std::vector<tools::wallet2::pending_tx> &ptx_vector)
{
  // count the number of old outputs
  std::string err;
  uint64_t bc_height = get_daemon_blockchain_height(err);
  if (!err.empty())
    return true;

  int max_n_old = 0;
  for (const auto &ptx: ptx_vector)
  {
    int n_old = 0;
    for (const auto i: ptx.selected_transfers)
    {
      const tools::wallet2::transfer_details &td = m_wallet->get_transfer_details(i);
      uint64_t age = bc_height - td.m_block_height;
      if (age > OLD_AGE_WARN_THRESHOLD)
        ++n_old;
    }
    max_n_old = std::max(max_n_old, n_old);
  }
  if (max_n_old > 1)
  {
    std::stringstream prompt;
    prompt << tr("此交易正在花费多个非常旧的输出。将它们分开发送会更有利于保护隐私。");
    prompt << ENDL << tr("仍要立即花费这些输出吗？");
    std::string accepted = input_line(prompt.str(), true);
    if (std::cin.eof())
      return false;
    if (!command_line::is_yes(accepted))
    {
      return false;
    }
  }
  return true;
}
//----------------------------------------------------------------------------------------------------
void simple_wallet::check_for_inactivity_lock(bool user)
{
  bool close_wallet = false;
  if (m_locked)
  {
#ifdef HAVE_READLINE
    PAUSE_READLINE();
    rdln::clear_screen();
#endif
    tools::clear_screen();
    m_in_command = true;
    if (!user)
    {
      const std::string speech = tr("I locked your Monero wallet to protect you while you were away\nsee \"help set\" to configure/disable");
      std::vector<std::pair<std::string, size_t>> lines = tools::split_string_by_width(speech, 45);

      size_t max_len = 0;
      for (const auto &i: lines)
        max_len = std::max(max_len, i.second);
      const size_t n_u = max_len + 2;
      tools::msg_writer() << " " << std::string(n_u, '_');
      for (size_t i = 0; i < lines.size(); ++i)
        tools::msg_writer() << (i == 0 ? "/" : i == lines.size() - 1 ? "\\" : "|") << " " << lines[i].first << std::string(max_len - lines[i].second, ' ') << " " << (i == 0 ? "\\" : i == lines.size() - 1 ? "/" : "|");
      tools::msg_writer() << " " << std::string(n_u, '-') << std::endl <<
          "        \\   (__)" << std::endl <<
          "         \\  (oo)\\_______" << std::endl <<
          "            (__)\\       )\\/\\" << std::endl <<
          "                ||----w |" << std::endl <<
          "                ||     ||" << std::endl <<
          "" << std::endl;
    }

    bool started_background_sync = false;
    if (!m_wallet->is_background_wallet() &&
        m_wallet->background_sync_type() != tools::wallet2::BackgroundSyncOff)
    {
      LOCK_IDLE_SCOPE();
      m_wallet->start_background_sync();
      started_background_sync = true;
    }

    while (1)
    {
      const char *inactivity_msg = user ? "" : tr("因长时间无操作而锁定。");
      tools::msg_writer() << inactivity_msg << (inactivity_msg[0] ? " " : "") << (
        (m_wallet->is_background_wallet() && m_wallet->background_sync_type() == tools::wallet2::BackgroundSyncCustomPassword)
            ? tr("解锁控制台需要后台密码。")
            : tr("解锁控制台需要钱包密码。")
      );

      if (m_wallet->is_background_syncing())
        tools::msg_writer() << tr("\nSyncing in the background while locked...") << std::endl;

      const bool show_wallet_name = m_wallet->show_wallet_name_when_locked();
      if (show_wallet_name)
      {
        tools::msg_writer() << tr("文件名：") << m_wallet->get_wallet_file();
        tools::msg_writer() << tr("网络类型：") << (
          m_wallet->nettype() == cryptonote::TESTNET ? tr("测试网") :
          m_wallet->nettype() == cryptonote::STAGENET ? tr("预发布网络") : tr("主网")
        );
      }
      try
      {
        bool read_failed = false;
        const auto pwd_container = get_and_verify_password(&read_failed);
        if (pwd_container)
        {
          if (started_background_sync)
          {
            LOCK_IDLE_SCOPE();
            m_wallet->stop_background_sync(pwd_container->password());
          }
          break;
        }
        if (read_failed)
        {
          // Password read was interrupted; close the wallet instead of looping back to the prompt
          close_wallet = true;
          break;
        }
      }
      catch (const std::exception &e)
      {
        // Report why unlocking failed, rather than just looping back to the password prompt
        auto writer = fail_msg_writer();
        if (show_wallet_name)
          writer << tr("解锁钱包失败：") << e.what();
        else
          writer << tr("解锁钱包失败。");
        if (m_wallet->key_on_device())
          writer << "\n" << tr("请确认硬件钱包已连接并解锁。");
      }
      catch (...) { /* do nothing, just let the loop loop */ }
    }
    m_last_activity_time = time(NULL);
    m_in_command = false;
    m_locked = false;
  }
  if (close_wallet) stop();
}
//----------------------------------------------------------------------------------------------------
bool simple_wallet::on_command(bool (simple_wallet::*cmd)(const std::vector<std::string>&), const std::vector<std::string> &args)
{
  m_last_activity_time = time(NULL);

  m_in_command = true;
  const epee::scope_guard scope_exit_handler([&](){
    m_last_activity_time = time(NULL);
    m_in_command = false;
  });

  check_for_inactivity_lock(false);
  return (this->*cmd)(args);
}
//----------------------------------------------------------------------------------------------------
bool simple_wallet::transfer_main(const std::vector<std::string> &args_, bool called_by_mms)
{
  if (!m_wallet)
  {
    fail_msg_writer() << tr("钱包为空");
    return true;
  }

//  "transfer [index=<N1>[,<N2>,...]] [<priority>] [<ring_size>] <address> <amount> [<payment_id>]"
  CHECK_IF_BACKGROUND_SYNCING("cannot transfer");
  if (!try_connect_to_daemon())
    return false;

  std::vector<std::string> local_args = args_;

  std::set<uint32_t> subaddr_indices;
  if (local_args.size() > 0 && local_args[0].substr(0, 6) == "index=")
  {
    if (!parse_subaddress_indices(local_args[0], subaddr_indices))
      return false;
    local_args.erase(local_args.begin());
  }

  fee_priority priority = m_wallet->get_default_priority();
  if (local_args.size() > 0 && parse_priority(local_args[0], priority))
    local_args.erase(local_args.begin());

  priority = m_wallet->adjust_priority(priority);

  size_t fake_outs_count = std::max<uint64_t>(m_wallet->get_min_ring_size(), 1) - 1;
  if(local_args.size() > 0) {
    size_t ring_size;
    if(!epee::string_tools::get_xtype_from_string(ring_size, local_args[0]))
    {
    }
    else if (ring_size == 0)
    {
      fail_msg_writer() << tr("环大小不能为 0");
      return false;
    }
    else
    {
      fake_outs_count = ring_size - 1;
      local_args.erase(local_args.begin());
    }
  }
  uint64_t adjusted_fake_outs_count = m_wallet->adjust_mixin(fake_outs_count);
  if (adjusted_fake_outs_count > fake_outs_count)
  {
    fail_msg_writer() << (boost::format(tr("环签名大小 %u 太小，最小值为 %u")) % (fake_outs_count+1) % (adjusted_fake_outs_count+1)).str();
    return false;
  }
  if (adjusted_fake_outs_count < fake_outs_count)
  {
    fail_msg_writer() << (boost::format(tr("环签名大小 %u 太大，最大值为 %u")) % (fake_outs_count+1) % (adjusted_fake_outs_count+1)).str();
    return false;
  }

  const size_t min_args = 1;
  if(local_args.size() < min_args)
  {
     fail_msg_writer() << tr("参数数量错误");
     return false;
  }

  std::vector<uint8_t> extra;
  bool payment_id_seen = false;
  if (!local_args.empty())
  {
    std::string payment_id_str = local_args.back();
    crypto::hash payment_id;
    bool r = true;
    if (tools::wallet2::parse_long_payment_id(payment_id_str, payment_id))
    {
      LONG_PAYMENT_ID_SUPPORT_CHECK();
    }
    if(!r)
    {
      fail_msg_writer() << tr("付款 ID 编码失败");
      return false;
    }
  }

  // Parse subtractfeefrom destination list
  tools::wallet2::unique_index_container subtract_fee_from_outputs;
  bool subtract_fee_from_all = false;
  for (auto it = local_args.begin(); it < local_args.end();)
  {
    bool matches = false;
    if (!parse_subtract_fee_from_outputs(*it, subtract_fee_from_outputs, subtract_fee_from_all, matches))
    {
      return false;
    }
    else if (matches)
    {
      it = local_args.erase(it);
      break;
    }
    else
    {
      ++it;
    }
  }

  vector<cryptonote::address_parse_info> dsts_info;
  vector<cryptonote::tx_destination_entry> dsts;
  for (size_t i = 0; i < local_args.size(); )
  {
    dsts_info.emplace_back();
    cryptonote::address_parse_info & info = dsts_info.back();
    cryptonote::tx_destination_entry de;
    bool r = true;

    // check for a URI
    std::string address_uri, payment_id_uri, tx_description, recipient_name, error;
    std::vector<std::string> unknown_parameters;
    uint64_t amount = 0;
    bool has_uri = m_wallet->parse_uri(local_args[i], address_uri, payment_id_uri, amount, tx_description, recipient_name, unknown_parameters, error);
    if (has_uri)
    {
      r = cryptonote::get_account_address_from_str_or_url(info, m_wallet->nettype(), address_uri, m_wallet->is_dns_enabled(), oa_prompter);
      if (payment_id_uri.size() == 16)
      {
        if (!tools::wallet2::parse_short_payment_id(payment_id_uri, info.payment_id))
        {
          fail_msg_writer() << tr("解析 URI 中的短付款 ID 失败");
          return false;
        }
        info.has_payment_id = true;
      }
      de.amount = amount;
      de.original = local_args[i];
      ++i;
    }
    else if (i + 1 < local_args.size())
    {
      r = cryptonote::get_account_address_from_str_or_url(info, m_wallet->nettype(), local_args[i], m_wallet->is_dns_enabled(), oa_prompter);
      bool ok = cryptonote::parse_amount(de.amount, local_args[i + 1]);
      if(!ok || 0 == de.amount)
      {
        fail_msg_writer() << tr("金额错误：") << local_args[i] << ' ' << local_args[i + 1] <<
          ", " << tr("expected number from 0 to ") << print_money(std::numeric_limits<uint64_t>::max());
        return false;
      }
      de.original = local_args[i];
      i += 2;
    }
    else
    {
      if (boost::starts_with(local_args[i], "monero:"))
        fail_msg_writer() << tr("最后一个参数无效：") << local_args.back() << ": " << error;
      else
        fail_msg_writer() << tr("最后一个参数无效：") << local_args.back();
      return false;
    }

    if (!r)
    {
      fail_msg_writer() << tr("解析地址失败");
      return false;
    }
    de.addr = info.address;
    de.is_subaddress = info.is_subaddress;
    de.is_integrated = info.has_payment_id;

    if (info.has_payment_id || !payment_id_uri.empty())
    {
      if (payment_id_seen)
      {
        fail_msg_writer() << tr("单笔交易不能使用多个付款 ID");
        return false;
      }

      crypto::hash payment_id;
      std::string extra_nonce;
      if (info.has_payment_id)
      {
        set_encrypted_payment_id_to_tx_extra_nonce(extra_nonce, info.payment_id);
      }
      else if (tools::wallet2::parse_payment_id(payment_id_uri, payment_id))
      {
        LONG_PAYMENT_ID_SUPPORT_CHECK();
      }
      else
      {
        fail_msg_writer() << tr("检测到付款 ID，但解析失败");
        return false;
      }
      bool r = add_extra_nonce_to_tx_extra(extra, extra_nonce);
      if(!r)
      {
        fail_msg_writer() << tr("支付 ID 已正确解码，但设置失败");
        return false;
      }
      payment_id_seen = true;
    }

    dsts.push_back(de);
  }

  if (subtract_fee_from_all)
  {
    subtract_fee_from_outputs.clear();
    for (decltype(subtract_fee_from_outputs)::value_type i = 0; i < dsts.size(); ++i)
      subtract_fee_from_outputs.insert(i);
  }

  SCOPED_WALLET_UNLOCK_ON_BAD_PASSWORD(return false;);

  try
  {
    // figure out what tx will be necessary
    auto ptx_vector = m_wallet->create_transactions_2(dsts, fake_outs_count, priority, extra,
      m_current_subaddress_account, subaddr_indices, subtract_fee_from_outputs);

    if (ptx_vector.empty())
    {
      fail_msg_writer() << tr("未找到输出，或守护进程尚未准备好");
      return false;
    }

    // if we need to check for backlog, check the worst case tx
    if (m_wallet->confirm_backlog())
    {
      std::stringstream prompt;
      double worst_fee_per_byte = std::numeric_limits<double>::max();
      for (size_t n = 0; n < ptx_vector.size(); ++n)
      {
        const uint64_t blob_size = cryptonote::tx_to_blob(ptx_vector[n].tx).size();
        const double fee_per_byte = ptx_vector[n].fee / (double)blob_size;
        if (fee_per_byte < worst_fee_per_byte)
        {
          worst_fee_per_byte = fee_per_byte;
        }
      }
      try
      {
        std::vector<std::pair<uint64_t, uint64_t>> nblocks = m_wallet->estimate_backlog({std::make_pair(worst_fee_per_byte, worst_fee_per_byte)});
        if (nblocks.size() != 1)
        {
          prompt << "Internal error checking for backlog. " << tr("即使如此也要继续吗？");
        }
        else
        {
          if (nblocks[0].first > m_wallet->get_confirm_backlog_threshold())
            prompt << (boost::format(tr("当前该手续费级别有 %u 个区块积压。确认继续吗？")) % nblocks[0].first).str();
        }
      }
      catch (const std::exception &e)
      {
        prompt << tr("检查交易积压失败：") << e.what() << ENDL << tr("即使如此也要继续吗？");
      }

      std::string prompt_str = prompt.str();
      if (!prompt_str.empty())
      {
        std::string accepted = input_line(prompt_str, true);
        if (std::cin.eof())
          return false;
        if (!command_line::is_yes(accepted))
        {
          fail_msg_writer() << tr("交易已取消。");

          return false; 
        }
      }
    }

    if (!prompt_if_old(ptx_vector))
    {
      fail_msg_writer() << tr("交易已取消。");
      return false;
    }

    // if more than one tx necessary, prompt user to confirm
    if (m_wallet->always_confirm_transfers() || ptx_vector.size() > 1)
    {
        uint64_t total_sent = 0;
        uint64_t total_fee = 0;
        uint64_t dust_not_in_fee = 0;
        uint64_t dust_in_fee = 0;
        for (size_t n = 0; n < ptx_vector.size(); ++n)
        {
          total_fee += ptx_vector[n].fee;
          for (auto i: ptx_vector[n].selected_transfers)
            total_sent += m_wallet->get_transfer_details(i).amount();
          total_sent -= ptx_vector[n].change_dts.amount + ptx_vector[n].fee;

          if (ptx_vector[n].dust_added_to_fee)
            dust_in_fee += ptx_vector[n].dust;
          else
            dust_not_in_fee += ptx_vector[n].dust;
        }

        std::stringstream prompt;
        for (size_t n = 0; n < ptx_vector.size(); ++n)
        {
          prompt << tr("\nTransaction ") << (n + 1) << "/" << ptx_vector.size() << ":\n";
          subaddr_indices.clear();
          for (uint32_t i : ptx_vector[n].construction_data.subaddr_indices)
            subaddr_indices.insert(i);
          for (uint32_t i : subaddr_indices)
            prompt << boost::format(tr("Spending from address index %d\n")) % i;
          if (subaddr_indices.size() > 1)
            prompt << tr("警告：正在同时使用多个地址的输出，这可能损害您的隐私。\n");
        }
        prompt << boost::format(tr("正在发送 %s。  ")) % print_money(total_sent);
        if (ptx_vector.size() > 1)
        {
          prompt << boost::format(tr("Your transaction needs to be split into %llu transactions.  "
            "This will result in a transaction fee being applied to each transaction, for a total fee of %s")) %
            ((unsigned long long)ptx_vector.size()) % print_money(total_fee);
        }
        else
        {
          prompt << boost::format(tr("交易手续费为 %s")) %
            print_money(total_fee);
        }
        if (dust_in_fee != 0) prompt << boost::format(tr("，其中 %s 是找零产生的零尘金额")) % print_money(dust_in_fee);
        if (dust_not_in_fee != 0)  prompt << tr(".") << ENDL << boost::format(tr("总计 %s 的零尘找零将发送到零尘地址")) 
                                                   % print_money(dust_not_in_fee);
        if (!process_ring_members(ptx_vector, prompt, m_wallet->print_ring_members()))
          return false;

        prompt << ENDL << tr("确认继续吗？");
        
        std::string accepted = input_line(prompt.str(), true);
        if (std::cin.eof())
          return false;
        if (!command_line::is_yes(accepted))
        {
          fail_msg_writer() << tr("交易已取消。");

          return false;
        }
    }

    // actually commit the transactions
    const multisig::multisig_account_status ms_status{m_wallet->get_multisig_status()};
    if (ms_status.multisig_is_active && called_by_mms)
    {
      std::string ciphertext = m_wallet->save_multisig_tx(ptx_vector);
      if (!ciphertext.empty())
      {
        get_message_store().process_wallet_created_data(get_multisig_wallet_state(), mms::message_type::partially_signed_tx, ciphertext);
        success_msg_writer(true) << tr("未签名交易已成功写入 MMS");
      }
    }
    else if (ms_status.multisig_is_active)
    {
      bool r = m_wallet->save_multisig_tx(ptx_vector, "multisig_monero_tx");
      if (!r)
      {
        fail_msg_writer() << tr("写入交易文件失败");
        return false;
      }
      else
      {
        success_msg_writer(true) << tr("未签名交易已成功写入文件：") << "multisig_monero_tx";
      }
    }
    else if (m_wallet->get_account().get_device().has_tx_cold_sign())
    {
      try
      {
        tools::wallet2::signed_tx_set signed_tx;
        if (!cold_sign_tx(ptx_vector, signed_tx, dsts_info, [&](const tools::wallet2::signed_tx_set &tx){ return accept_loaded_tx(tx); })){
          fail_msg_writer() << tr("使用硬件钱包冷签名交易失败");
          return false;
        }

        commit_or_save(signed_tx.ptx, m_do_not_relay);
      }
      catch (const std::exception& e)
      {
        handle_transfer_exception(std::current_exception(), m_wallet->is_trusted_daemon());
        return false;
      }
      catch (...)
      {
        LOG_ERROR("Unknown error");
        fail_msg_writer() << tr("未知错误");
        return false;
      }
    }
    else if (m_wallet->watch_only())
    {
      bool r = m_wallet->save_tx(ptx_vector, "unsigned_monero_tx");
      if (!r)
      {
        fail_msg_writer() << tr("写入交易文件失败");
        return false;
      }
      else
      {
        success_msg_writer(true) << tr("未签名交易已成功写入文件：") << "unsigned_monero_tx";
      }
    }
    else
    {
      commit_or_save(ptx_vector, m_do_not_relay);
    }
  }
  catch (const std::exception &e)
  {
    handle_transfer_exception(std::current_exception(), m_wallet->is_trusted_daemon());
    return false;
  }
  catch (...)
  {
    LOG_ERROR("未知错误");
    fail_msg_writer() << tr("未知错误");
    return false;
  }

  return true;
}
//----------------------------------------------------------------------------------------------------
bool simple_wallet::transfer(const std::vector<std::string> &args_)
{
  CHECK_IF_BACKGROUND_SYNCING("cannot transfer");
  if (args_.size() < 1)
  {
    PRINT_USAGE(USAGE_TRANSFER);
    return true;
  }
  transfer_main(args_, false);
  return true;
}
//----------------------------------------------------------------------------------------------------

bool simple_wallet::sweep_unmixable(const std::vector<std::string> &args_)
{
  CHECK_IF_BACKGROUND_SYNCING("cannot sweep");
  if (!try_connect_to_daemon())
    return true;

  SCOPED_WALLET_UNLOCK();

  try
  {
    // figure out what tx will be necessary
    auto ptx_vector = m_wallet->create_unmixable_sweep_transactions();

    if (ptx_vector.empty())
    {
      fail_msg_writer() << tr("未找到无法混合的输出");
      return true;
    }

    // give user total and fee, and prompt to confirm
    uint64_t total_fee = 0, total_unmixable = 0;
    for (size_t n = 0; n < ptx_vector.size(); ++n)
    {
      total_fee += ptx_vector[n].fee;
      for (auto i: ptx_vector[n].selected_transfers)
        total_unmixable += m_wallet->get_transfer_details(i).amount();
    }

    std::string prompt_str = tr("正在清扫 ") + print_money(total_unmixable);
    if (ptx_vector.size() > 1) {
      prompt_str = (boost::format(tr("正在通过 %llu 笔交易清扫 %s，手续费总计 %s。确认继续吗？")) %
        print_money(total_unmixable) %
        ((unsigned long long)ptx_vector.size()) %
        print_money(total_fee)).str();
    }
    else {
      prompt_str = (boost::format(tr("正在清扫 %s，手续费总计 %s。确认继续吗？")) %
        print_money(total_unmixable) %
        print_money(total_fee)).str();
    }
    std::string accepted = input_line(prompt_str, true);
    if (std::cin.eof())
      return true;
    if (!command_line::is_yes(accepted))
    {
      fail_msg_writer() << tr("交易已取消。");

      return true;
    }

    // actually commit the transactions
    if (m_wallet->get_multisig_status().multisig_is_active)
    {
      CHECK_MULTISIG_ENABLED();
      bool r = m_wallet->save_multisig_tx(ptx_vector, "multisig_monero_tx");
      if (!r)
      {
        fail_msg_writer() << tr("写入交易文件失败");
      }
      else
      {
        success_msg_writer(true) << tr("未签名交易已成功写入文件：") << "multisig_monero_tx";
      }
    }
    else if (m_wallet->watch_only())
    {
      bool r = m_wallet->save_tx(ptx_vector, "unsigned_monero_tx");
      if (!r)
      {
        fail_msg_writer() << tr("写入交易文件失败");
      }
      else
      {
        success_msg_writer(true) << tr("未签名交易已成功写入文件：") << "unsigned_monero_tx";
      }
    }
    else
    {
      commit_or_save(ptx_vector, m_do_not_relay);
    }
  }
  catch (const tools::error::not_enough_unlocked_money& e)
  {
    fail_msg_writer() << tr("可用余额不足");
    std::string accepted = input_line((boost::format(tr("Discarding %s of unmixable outputs that cannot be spent, which can be undone by \"rescan_spent\".  确认继续吗？")) % print_money(e.available())).str(), true);
    if (std::cin.eof())
      return true;
    if (command_line::is_yes(accepted))
    {
      try
      {
        m_wallet->discard_unmixable_outputs();
      } catch (...) {}
    }
  }
  catch (const std::exception &e)
  {
    handle_transfer_exception(std::current_exception(), m_wallet->is_trusted_daemon());
  }
  catch (...)
  {
    LOG_ERROR("未知错误");
    fail_msg_writer() << tr("未知错误");
  }

  return true;
}
//----------------------------------------------------------------------------------------------------
bool simple_wallet::sweep_main(uint32_t account, uint64_t below, const std::vector<std::string> &args_)
{
  CHECK_IF_BACKGROUND_SYNCING("cannot sweep");
  auto print_usage = [this, account, below]()
  {
    if (below)
    {
      PRINT_USAGE(USAGE_SWEEP_BELOW);
    }
    else if (account == m_current_subaddress_account)
    {
      PRINT_USAGE(USAGE_SWEEP_ALL);
    }
    else
    {
      PRINT_USAGE(USAGE_SWEEP_ACCOUNT);
    }
  };
  if (args_.size() == 0)
  {
    fail_msg_writer() << tr("未提供地址");
    print_usage();
    return true;
  }

  if (!try_connect_to_daemon())
    return true;

  std::vector<std::string> local_args = args_;

  std::set<uint32_t> subaddr_indices;
  for (auto it = local_args.begin(); it != local_args.end(); ++it)
  {
    if (it->substr(0, 6) != "index=")
      continue;
    if (*it == "index=all")
    {
      for (uint32_t i = 0; i < m_wallet->get_num_subaddresses(account); ++i)
        subaddr_indices.insert(i);
    }
    else if (!parse_subaddress_indices(*it, subaddr_indices))
    {
      print_usage();
      return true;
    }
    local_args.erase(it);
    break;
  }

  fee_priority priority = fee_priority::Default;
  if (local_args.size() > 0 && parse_priority(local_args[0], priority))
    local_args.erase(local_args.begin());

  priority = m_wallet->adjust_priority(priority);

  size_t fake_outs_count = std::max<uint64_t>(m_wallet->get_min_ring_size(), 1) - 1;
  if(local_args.size() > 0) {
    size_t ring_size;
    if(!epee::string_tools::get_xtype_from_string(ring_size, local_args[0]))
    {
    }
    else if (ring_size == 0)
    {
      fail_msg_writer() << tr("环大小不能为 0");
      return true;
    }
    else
    {
      fake_outs_count = ring_size - 1;
      local_args.erase(local_args.begin());
    }
  }
  uint64_t adjusted_fake_outs_count = m_wallet->adjust_mixin(fake_outs_count);
  if (adjusted_fake_outs_count > fake_outs_count)
  {
    fail_msg_writer() << (boost::format(tr("环签名大小 %u 太小，最小值为 %u")) % (fake_outs_count+1) % (adjusted_fake_outs_count+1)).str();
    return true;
  }
  if (adjusted_fake_outs_count < fake_outs_count)
  {
    fail_msg_writer() << (boost::format(tr("环签名大小 %u 太大，最大值为 %u")) % (fake_outs_count+1) % (adjusted_fake_outs_count+1)).str();
    return true;
  }

  size_t outputs = 1;
  if (local_args.size() > 0 && local_args[0].substr(0, 8) == "outputs=")
  {
    if (!epee::string_tools::get_xtype_from_string(outputs, local_args[0].substr(8)))
    {
      fail_msg_writer() << tr("解析输出数量失败");
      return true;
    }
    else if (outputs < 1)
    {
      fail_msg_writer() << tr("输出数量必须大于 0");
      return true;
    }
    else
    {
      local_args.erase(local_args.begin());
    }
  }

  std::vector<uint8_t> extra;
  bool payment_id_seen = false;
  if (local_args.size() >= 2)
  {
    std::string payment_id_str = local_args.back();

    crypto::hash payment_id;
    bool r = tools::wallet2::parse_long_payment_id(payment_id_str, payment_id);
    if(r)
    {
      LONG_PAYMENT_ID_SUPPORT_CHECK();
    }

    if(!r && local_args.size() == 3)
    {
      fail_msg_writer() << tr("payment id has invalid format, expected 16 or 64 character hex string: ") << payment_id_str;
      print_usage();
      return true;
    }
    if (payment_id_seen)
      local_args.pop_back();
  }

  if (local_args.empty())
  {
    fail_msg_writer() << tr("未提供地址");
    print_usage();
    return true;
  }

  cryptonote::address_parse_info info;
  if (!cryptonote::get_account_address_from_str_or_url(info, m_wallet->nettype(), local_args[0], m_wallet->is_dns_enabled(), oa_prompter))
  {
    fail_msg_writer() << tr("解析地址失败");
    print_usage();
    return true;
  }

  if (info.has_payment_id)
  {
    if (payment_id_seen)
    {
      fail_msg_writer() << tr("单笔交易不能使用多个付款 ID: ") << local_args[0];
      return true;
    }

    std::string extra_nonce;
    set_encrypted_payment_id_to_tx_extra_nonce(extra_nonce, info.payment_id);
    bool r = add_extra_nonce_to_tx_extra(extra, extra_nonce);
    if(!r)
    {
      fail_msg_writer() << tr("支付 ID 已正确解码，但设置失败");
      return true;
    }
    payment_id_seen = true;
  }

  SCOPED_WALLET_UNLOCK();

  try
  {
    // figure out what tx will be necessary
    auto ptx_vector = m_wallet->create_transactions_all(below, info.address, info.is_subaddress, outputs, fake_outs_count, priority, extra, account, subaddr_indices);

    if (ptx_vector.empty())
    {
      fail_msg_writer() << tr("未找到输出，或守护进程尚未准备好");
      return true;
    }

    if (!prompt_if_old(ptx_vector))
    {
      fail_msg_writer() << tr("交易已取消。");
      return false;
    }

    // give user total and fee, and prompt to confirm
    uint64_t total_fee = 0, total_sent = 0;
    for (size_t n = 0; n < ptx_vector.size(); ++n)
    {
      total_fee += ptx_vector[n].fee;
      for (auto i: ptx_vector[n].selected_transfers)
        total_sent += m_wallet->get_transfer_details(i).amount();
    }

    std::ostringstream prompt;
    for (size_t n = 0; n < ptx_vector.size(); ++n)
    {
      prompt << tr("\nTransaction ") << (n + 1) << "/" << ptx_vector.size() << ":\n";
      subaddr_indices.clear();
      for (uint32_t i : ptx_vector[n].construction_data.subaddr_indices)
        subaddr_indices.insert(i);
      for (uint32_t i : subaddr_indices)
        prompt << boost::format(tr("Spending from address index %d\n")) % i;
      if (subaddr_indices.size() > 1)
        prompt << tr("警告：正在同时使用多个地址的输出，这可能损害您的隐私。\n");
    }
    if (!process_ring_members(ptx_vector, prompt, m_wallet->print_ring_members()))
      return true;
    if (ptx_vector.size() > 1) {
      prompt << boost::format(tr("正在通过 %llu 笔交易清扫 %s，手续费总计 %s。确认继续吗？")) %
        print_money(total_sent) %
        ((unsigned long long)ptx_vector.size()) %
        print_money(total_fee);
    }
    else {
      prompt << boost::format(tr("正在清扫 %s，手续费总计 %s。确认继续吗？")) %
        print_money(total_sent) %
        print_money(total_fee);
    }
    std::string accepted = input_line(prompt.str(), true);
    if (std::cin.eof())
      return true;
    if (!command_line::is_yes(accepted))
    {
      fail_msg_writer() << tr("交易已取消。");

      return true;
    }

    // actually commit the transactions
    if (m_wallet->get_multisig_status().multisig_is_active)
    {
      CHECK_MULTISIG_ENABLED();
      bool r = m_wallet->save_multisig_tx(ptx_vector, "multisig_monero_tx");
      if (!r)
      {
        fail_msg_writer() << tr("写入交易文件失败");
      }
      else
      {
        success_msg_writer(true) << tr("未签名交易已成功写入文件：") << "multisig_monero_tx";
      }
    }
    else if (m_wallet->get_account().get_device().has_tx_cold_sign())
    {
      try
      {
        tools::wallet2::signed_tx_set signed_tx;
        std::vector<cryptonote::address_parse_info> dsts_info;
        dsts_info.push_back(info);

        if (!cold_sign_tx(ptx_vector, signed_tx, dsts_info, [&](const tools::wallet2::signed_tx_set &tx){ return accept_loaded_tx(tx); })){
          fail_msg_writer() << tr("使用硬件钱包冷签名交易失败");
          return true;
        }

        commit_or_save(signed_tx.ptx, m_do_not_relay);
      }
      catch (const std::exception& e)
      {
        handle_transfer_exception(std::current_exception(), m_wallet->is_trusted_daemon());
      }
      catch (...)
      {
        LOG_ERROR("Unknown error");
        fail_msg_writer() << tr("未知错误");
      }
    }
    else if (m_wallet->watch_only())
    {
      bool r = m_wallet->save_tx(ptx_vector, "unsigned_monero_tx");
      if (!r)
      {
        fail_msg_writer() << tr("写入交易文件失败");
      }
      else
      {
        success_msg_writer(true) << tr("未签名交易已成功写入文件：") << "unsigned_monero_tx";
      }
    }
    else
    {
      commit_or_save(ptx_vector, m_do_not_relay);
    }
  }
  catch (const std::exception& e)
  {
    handle_transfer_exception(std::current_exception(), m_wallet->is_trusted_daemon());
  }
  catch (...)
  {
    LOG_ERROR("未知错误");
    fail_msg_writer() << tr("未知错误");
  }

  return true;
}
//----------------------------------------------------------------------------------------------------
bool simple_wallet::sweep_single(const std::vector<std::string> &args_)
{
  CHECK_IF_BACKGROUND_SYNCING("cannot sweep");
  if (!try_connect_to_daemon())
    return true;

  std::vector<std::string> local_args = args_;

  fee_priority priority = fee_priority::Default;
  if (local_args.size() > 0 && parse_priority(local_args[0], priority))
    local_args.erase(local_args.begin());

  priority = m_wallet->adjust_priority(priority);

  size_t fake_outs_count = std::max<uint64_t>(m_wallet->get_min_ring_size(), 1) - 1;
  if(local_args.size() > 0) {
    size_t ring_size;
    if(!epee::string_tools::get_xtype_from_string(ring_size, local_args[0]))
    {
    }
    else if (ring_size == 0)
    {
      fail_msg_writer() << tr("环大小不能为 0");
      return true;
    }
    else
    {
      fake_outs_count = ring_size - 1;
      local_args.erase(local_args.begin());
    }
  }
  uint64_t adjusted_fake_outs_count = m_wallet->adjust_mixin(fake_outs_count);
  if (adjusted_fake_outs_count > fake_outs_count)
  {
    fail_msg_writer() << (boost::format(tr("环签名大小 %u 太小，最小值为 %u")) % (fake_outs_count+1) % (adjusted_fake_outs_count+1)).str();
    return true;
  }
  if (adjusted_fake_outs_count < fake_outs_count)
  {
    fail_msg_writer() << (boost::format(tr("环签名大小 %u 太大，最大值为 %u")) % (fake_outs_count+1) % (adjusted_fake_outs_count+1)).str();
    return true;
  }

  size_t outputs = 1;
  if (local_args.size() > 0 && local_args[0].substr(0, 8) == "outputs=")
  {
    if (!epee::string_tools::get_xtype_from_string(outputs, local_args[0].substr(8)))
    {
      fail_msg_writer() << tr("解析输出数量失败");
      return true;
    }
    else if (outputs < 1)
    {
      fail_msg_writer() << tr("输出数量必须大于 0");
      return true;
    }
    else
    {
      local_args.erase(local_args.begin());
    }
  }

  std::vector<uint8_t> extra;
  bool payment_id_seen = false;
  if (local_args.size() == 3)
  {
    crypto::hash payment_id;
    std::string extra_nonce;
    if (tools::wallet2::parse_long_payment_id(local_args.back(), payment_id))
    {
      LONG_PAYMENT_ID_SUPPORT_CHECK();
    }
    else
    {
      fail_msg_writer() << tr("解析支付 ID 失败");
      return true;
    }

    if (!add_extra_nonce_to_tx_extra(extra, extra_nonce))
    {
      fail_msg_writer() << tr("支付 ID 已正确解码，但设置失败");
      return true;
    }

    local_args.pop_back();
    payment_id_seen = true;
  }

  if (local_args.size() != 2)
  {
    PRINT_USAGE(USAGE_SWEEP_SINGLE);
    return true;
  }

  crypto::key_image ki;
  if (!epee::string_tools::hex_to_pod(local_args[0], ki))
  {
    fail_msg_writer() << tr("解析密钥镜像失败");
    return true;
  }

  cryptonote::address_parse_info info;
  if (!cryptonote::get_account_address_from_str_or_url(info, m_wallet->nettype(), local_args[1], m_wallet->is_dns_enabled(), oa_prompter))
  {
    fail_msg_writer() << tr("解析地址失败");
    return true;
  }

  if (info.has_payment_id)
  {
    if (payment_id_seen)
    {
      fail_msg_writer() << tr("单笔交易不能使用多个付款 ID: ") << local_args[0];
      return true;
    }

    std::string extra_nonce;
    set_encrypted_payment_id_to_tx_extra_nonce(extra_nonce, info.payment_id);
    if (!add_extra_nonce_to_tx_extra(extra, extra_nonce))
    {
      fail_msg_writer() << tr("支付 ID 已正确解码，但设置失败");
      return true;
    }
    payment_id_seen = true;
  }

  SCOPED_WALLET_UNLOCK();

  try
  {
    // figure out what tx will be necessary
    auto ptx_vector = m_wallet->create_transactions_single(ki, info.address, info.is_subaddress, outputs, fake_outs_count, priority, extra);

    if (ptx_vector.empty())
    {
      fail_msg_writer() << tr("未找到输出");
      return true;
    }
    if (ptx_vector.size() > 1)
    {
      fail_msg_writer() << tr("创建了多个交易，这是不应该发生的");
      return true;
    }
    if (ptx_vector[0].selected_transfers.size() != 1)
    {
      fail_msg_writer() << tr("交易使用了多个输入或没有输入，这种情况不应发生");
      return true;
    }

    // give user total and fee, and prompt to confirm
    uint64_t total_fee = ptx_vector[0].fee;
    uint64_t total_sent = m_wallet->get_transfer_details(ptx_vector[0].selected_transfers.front()).amount();
    std::ostringstream prompt;
    if (!process_ring_members(ptx_vector, prompt, m_wallet->print_ring_members()))
      return true;
    prompt << boost::format(tr("正在清扫 %s，手续费总计 %s。确认继续吗？")) %
      print_money(total_sent) %
      print_money(total_fee);
    std::string accepted = input_line(prompt.str(), true);
    if (std::cin.eof())
      return true;
    if (!command_line::is_yes(accepted))
    {
      fail_msg_writer() << tr("交易已取消。");
      return true;
    }

    // actually commit the transactions
    if (m_wallet->get_multisig_status().multisig_is_active)
    {
      CHECK_MULTISIG_ENABLED();
      bool r = m_wallet->save_multisig_tx(ptx_vector, "multisig_monero_tx");
      if (!r)
      {
        fail_msg_writer() << tr("写入交易文件失败");
      }
      else
      {
        success_msg_writer(true) << tr("未签名交易已成功写入文件：") << "multisig_monero_tx";
      }
    }
    else if (m_wallet->get_account().get_device().has_tx_cold_sign())
    {
      try
      {
        tools::wallet2::signed_tx_set signed_tx;
        std::vector<cryptonote::address_parse_info> dsts_info;
        dsts_info.push_back(info);

        if (!cold_sign_tx(ptx_vector, signed_tx, dsts_info, [&](const tools::wallet2::signed_tx_set &tx){ return accept_loaded_tx(tx); })){
          fail_msg_writer() << tr("使用硬件钱包冷签名交易失败");
          return true;
        }

        commit_or_save(signed_tx.ptx, m_do_not_relay);
      }
      catch (const std::exception& e)
      {
        handle_transfer_exception(std::current_exception(), m_wallet->is_trusted_daemon());
      }
      catch (...)
      {
        LOG_ERROR("Unknown error");
        fail_msg_writer() << tr("未知错误");
      }
    }
    else if (m_wallet->watch_only())
    {
      bool r = m_wallet->save_tx(ptx_vector, "unsigned_monero_tx");
      if (!r)
      {
        fail_msg_writer() << tr("写入交易文件失败");
      }
      else
      {
        success_msg_writer(true) << tr("未签名交易已成功写入文件：") << "unsigned_monero_tx";
      }
    }
    else
    {
      commit_or_save(ptx_vector, m_do_not_relay);
    }

  }
  catch (const std::exception& e)
  {
    handle_transfer_exception(std::current_exception(), m_wallet->is_trusted_daemon());
  }
  catch (...)
  {
    LOG_ERROR("未知错误");
    fail_msg_writer() << tr("未知错误");
  }

  return true;
}
//----------------------------------------------------------------------------------------------------
bool simple_wallet::sweep_all(const std::vector<std::string> &args_)
{
  CHECK_IF_BACKGROUND_SYNCING("cannot sweep");
  sweep_main(m_current_subaddress_account, 0, args_);
  return true;
}
//----------------------------------------------------------------------------------------------------
bool simple_wallet::sweep_account(const std::vector<std::string> &args_)
{
  CHECK_IF_BACKGROUND_SYNCING("cannot sweep");
  auto local_args = args_;
  if (local_args.empty())
  {
    PRINT_USAGE(USAGE_SWEEP_ACCOUNT);
    return true;
  }
  uint32_t account = 0;
  if (!epee::string_tools::get_xtype_from_string(account, local_args[0]))
  {
    fail_msg_writer() << tr("账户无效");
    return true;
  }
  local_args.erase(local_args.begin());

  sweep_main(account, 0, local_args);
  return true;
}
//----------------------------------------------------------------------------------------------------
bool simple_wallet::sweep_below(const std::vector<std::string> &args_)
{
  CHECK_IF_BACKGROUND_SYNCING("cannot sweep");
  uint64_t below = 0;
  if (args_.size() < 1)
  {
    fail_msg_writer() << tr("缺少阈值金额");
    PRINT_USAGE(USAGE_SWEEP_BELOW);
    return true;
  }
  if (!cryptonote::parse_amount(below, args_[0]))
  {
    fail_msg_writer() << tr("金额阈值无效");
    return true;
  }
  sweep_main(m_current_subaddress_account, below, std::vector<std::string>(++args_.begin(), args_.end()));
  return true;
}
//----------------------------------------------------------------------------------------------------
bool simple_wallet::donate(const std::vector<std::string> &args_)
{
  CHECK_IF_BACKGROUND_SYNCING("cannot donate");
  std::vector<std::string> local_args = args_;
  if(local_args.empty() || local_args.size() > 4)
  {
     PRINT_USAGE(USAGE_DONATE);
     return true;
  }
  std::string amount_str;
  // get amount and pop
  uint64_t amount;
  bool ok = cryptonote::parse_amount(amount, local_args.back());
  if (ok && amount != 0)
  {
    amount_str = local_args.back();
    local_args.pop_back();
  }
  else
  { 
    fail_msg_writer() << tr("金额错误：") << local_args.back() << ", " << tr("expected number from 0 to ") << print_money(std::numeric_limits<uint64_t>::max());
    return true;
  }
  // push back address, amount
  if (m_wallet->nettype() != cryptonote::MAINNET)
  {
    fail_msg_writer() << tr("捐赠仅支持主网。");
    return true;
  }
  local_args.push_back(MONERO_DONATION_ADDR);
  local_args.push_back(amount_str);
  message_writer() << (boost::format(tr("正在向 Monero 项目捐赠 %s %s（donate.getmonero.org 或 %s）。")) % amount_str % cryptonote::get_unit(cryptonote::get_default_decimal_point()) % MONERO_DONATION_ADDR).str();
  transfer(local_args);
  return true;
}
//----------------------------------------------------------------------------------------------------
bool simple_wallet::accept_loaded_tx(const std::function<size_t()> get_num_txes, const std::function<const tools::wallet2::tx_construction_data&(size_t)> &get_tx, const std::string &extra_message)
{
  CHECK_IF_BACKGROUND_SYNCING("cannot load tx");
  // gather info to ask the user
  uint64_t amount = 0, amount_to_dests = 0, change = 0;
  size_t min_ring_size = ~0;
  std::unordered_map<cryptonote::account_public_address, std::pair<std::string, uint64_t>> dests;
  int first_known_non_zero_change_index = -1;
  std::string payment_id_string = "";
  for (size_t n = 0; n < get_num_txes(); ++n)
  {
    const tools::wallet2::tx_construction_data &cd = get_tx(n);

    std::vector<tx_extra_field> tx_extra_fields;
    bool has_encrypted_payment_id = false;
    crypto::hash8 payment_id8 = crypto::null_hash8;
    if (cryptonote::parse_tx_extra(cd.extra, tx_extra_fields))
    {
      tx_extra_nonce extra_nonce;
      if (find_tx_extra_field_by_type(tx_extra_fields, extra_nonce))
      {
        crypto::hash payment_id;
        if(get_encrypted_payment_id_from_tx_extra_nonce(extra_nonce.nonce, payment_id8))
        {
          if (!payment_id_string.empty())
            payment_id_string += ", ";

          // if none of the addresses are integrated addresses, it's a dummy one
          bool is_dummy = true;
          for (const auto &e: cd.dests)
            if (e.is_integrated)
              is_dummy = false;

          CHECK_AND_ASSERT_MES(is_dummy == (payment_id8 == crypto::null_hash8), false, "Bad loaded tx: mismatched payment ID info");

          if (is_dummy)
          {
            payment_id_string += std::string("dummy encrypted payment ID");
          }
          else
          {
            payment_id_string += std::string("encrypted payment ID ") + epee::string_tools::pod_to_hex(payment_id8);
            has_encrypted_payment_id = true;
          }
        }
        else if (get_payment_id_from_tx_extra_nonce(extra_nonce.nonce, payment_id))
        {
          if (!payment_id_string.empty())
            payment_id_string += ", ";
          payment_id_string += std::string("unencrypted payment ID ") + epee::string_tools::pod_to_hex(payment_id);
          payment_id_string += " (OBSOLETE)";
        }
      }
    }

    for (size_t s = 0; s < cd.sources.size(); ++s)
    {
      amount += cd.sources[s].amount;
      size_t ring_size = cd.sources[s].outputs.size();
      if (ring_size < min_ring_size)
        min_ring_size = ring_size;
    }
    for (size_t d = 0; d < cd.splitted_dsts.size(); ++d)
    {
      const tx_destination_entry &entry = cd.splitted_dsts[d];
      std::string address, standard_address = get_account_address_as_str(m_wallet->nettype(), entry.is_subaddress, entry.addr);
      if (has_encrypted_payment_id && !entry.is_subaddress)
      {
        address = get_account_integrated_address_as_str(m_wallet->nettype(), entry.addr, payment_id8);
        address += std::string(" (" + standard_address + " with encrypted payment id " + epee::string_tools::pod_to_hex(payment_id8) + ")");
      }
      else
        address = standard_address;
      auto i = dests.find(entry.addr);
      if (i == dests.end())
        dests.insert(std::make_pair(entry.addr, std::make_pair(address, entry.amount)));
      else
        i->second.second += entry.amount;
      amount_to_dests += entry.amount;
    }
    if (cd.change_dts.amount > 0)
    {
      auto it = dests.find(cd.change_dts.addr);
      if (it == dests.end())
      {
        fail_msg_writer() << tr("找回的找零没有发送到已支付地址");
        return false;
      }
      if (it->second.second < cd.change_dts.amount)
      {
        fail_msg_writer() << tr("Claimed change is larger than payment to the change address");
        return false;
      }
      if (cd.change_dts.amount > 0)
      {
        if (first_known_non_zero_change_index == -1)
          first_known_non_zero_change_index = n;
        if (memcmp(&cd.change_dts.addr, &get_tx(first_known_non_zero_change_index).change_dts.addr, sizeof(cd.change_dts.addr)))
        {
          fail_msg_writer() << tr("找零发送到了多个地址");
          return false;
        }
      }
      change += cd.change_dts.amount;
      it->second.second -= cd.change_dts.amount;
      if (it->second.second == 0)
        dests.erase(cd.change_dts.addr);
    }
  }

  if (payment_id_string.empty())
    payment_id_string = "no payment ID";

  std::string dest_string;
  size_t n_dummy_outputs = 0;
  for (auto i = dests.begin(); i != dests.end(); )
  {
    if (i->second.second > 0)
    {
      if (!dest_string.empty())
        dest_string += ", ";
      dest_string += (boost::format(tr("sending %s to %s")) % print_money(i->second.second) % i->second.first).str();
    }
    else
      ++n_dummy_outputs;
    ++i;
  }
  if (n_dummy_outputs > 0)
  {
    if (!dest_string.empty())
      dest_string += ", ";
    dest_string += std::to_string(n_dummy_outputs) + tr(" dummy output(s)");
  }
  if (dest_string.empty())
    dest_string = tr("with no destinations");

  std::string change_string;
  if (change > 0)
  {
    const tools::wallet2::tx_construction_data &cd = get_tx(first_known_non_zero_change_index);
    std::string address = get_account_address_as_str(m_wallet->nettype(), cd.subaddr_account > 0, cd.change_dts.addr);
    change_string += (boost::format(tr("%s change to %s")) % print_money(change) % address).str();
  }
  else
    change_string += tr("无找零");

  uint64_t fee = amount - amount_to_dests;
  std::string prompt_str = (boost::format(tr("Loaded %lu transactions, for %s, fee %s, %s, %s, with min ring size %lu, %s. %s确认继续吗？")) % (unsigned long)get_num_txes() % print_money(amount) % print_money(fee) % dest_string % change_string % (unsigned long)min_ring_size % payment_id_string % extra_message).str();
  return command_line::is_yes(input_line(prompt_str, true));
}
//----------------------------------------------------------------------------------------------------
bool simple_wallet::accept_loaded_tx(const tools::wallet2::unsigned_tx_set &txs)
{
  std::string extra_message;
  if (!std::get<2>(txs.new_transfers).empty())
    extra_message = (boost::format("%u outputs to import. ") % (unsigned)std::get<2>(txs.new_transfers).size()).str();
  else if (!std::get<2>(txs.transfers).empty())
    extra_message = (boost::format("%u outputs to import. ") % (unsigned)std::get<2>(txs.transfers).size()).str();
  return accept_loaded_tx([&txs](){return txs.txes.size();}, [&txs](size_t n)->const tools::wallet2::tx_construction_data&{return txs.txes[n];}, extra_message);
}
//----------------------------------------------------------------------------------------------------
bool simple_wallet::accept_loaded_tx(const tools::wallet2::signed_tx_set &txs)
{
  std::string extra_message;
  if (!txs.key_images.empty())
    extra_message = (boost::format("%u key images to import. ") % (unsigned)txs.key_images.size()).str();
  return accept_loaded_tx([&txs](){return txs.ptx.size();}, [&txs](size_t n)->const tools::wallet2::tx_construction_data&{return txs.ptx[n].construction_data;}, extra_message);
}
//----------------------------------------------------------------------------------------------------
bool simple_wallet::sign_transfer(const std::vector<std::string> &args_)
{
  if (m_wallet->key_on_device())
  {
    fail_msg_writer() << tr("硬件钱包不支持此命令");
    return true;
  }
  if(m_wallet->get_multisig_status().multisig_is_active)
  {
     fail_msg_writer() << tr("这是多重签名钱包，只能使用 sign_multisig 进行签名");
     return true;
  }
  if(m_wallet->watch_only())
  {
     fail_msg_writer() << tr("这是仅观察钱包");
     return true;
  }
  CHECK_IF_BACKGROUND_SYNCING("cannot sign transfer");

  bool export_raw = false;
  std::string unsigned_filename = "unsigned_monero_tx";
  if (args_.size() > 2 || (args_.size() == 2 && args_[0] != "export_raw"))
  {
    PRINT_USAGE(USAGE_SIGN_TRANSFER);
    return true;
  }
  else if (args_.size() == 2)
  {
    export_raw = true;
    unsigned_filename = args_[1];
  }
  else if (args_.size() == 1)
  {
    if (args_[0] == "export_raw")
      export_raw = true;
    else
      unsigned_filename = args_[0];
  }

  SCOPED_WALLET_UNLOCK();

  std::vector<tools::wallet2::pending_tx> ptx;
  try
  {
    bool r = m_wallet->sign_tx(unsigned_filename, "signed_monero_tx", ptx, [&](const tools::wallet2::unsigned_tx_set &tx){ return accept_loaded_tx(tx); }, export_raw);
    if (!r)
    {
      fail_msg_writer() << tr("签署交易失败");
      return true;
    }
  }
  catch (const std::exception &e)
  {
    fail_msg_writer() << tr("签署交易失败: ") << e.what();
    return true;
  }

  std::string txids_as_text;
  for (const auto &t: ptx)
  {
    if (!txids_as_text.empty())
      txids_as_text += (", ");
    txids_as_text += epee::string_tools::pod_to_hex(get_transaction_hash(t.tx));
  }
  success_msg_writer(true) << tr("交易已成功签名并保存到文件 ") << "signed_monero_tx" << ", txid " << txids_as_text;
  if (export_raw)
  {
    std::string rawfiles_as_text;
    for (size_t i = 0; i < ptx.size(); ++i)
    {
      if (i > 0)
        rawfiles_as_text += ", ";
      rawfiles_as_text += "signed_monero_tx_raw" + (ptx.size() == 1 ? "" : ("_" + std::to_string(i)));
    }
    success_msg_writer(true) << tr("交易原始十六进制数据已导出到 ") << rawfiles_as_text;
  }
  return true;
}
//----------------------------------------------------------------------------------------------------
bool simple_wallet::submit_transfer(const std::vector<std::string> &args_)
{
  if (m_wallet->key_on_device())
  {
    fail_msg_writer() << tr("硬件钱包不支持此命令");
    return true;
  }
  if (!try_connect_to_daemon())
    return true;

  try
  {
    std::vector<tools::wallet2::pending_tx> ptx_vector;
    bool r = m_wallet->load_tx("signed_monero_tx", ptx_vector, [&](const tools::wallet2::signed_tx_set &tx){ return accept_loaded_tx(tx); });
    if (!r)
    {
      fail_msg_writer() << tr("从文件加载交易失败");
      return true;
    }

    commit_or_save(ptx_vector, false);
  }
  catch (const std::exception& e)
  {
    handle_transfer_exception(std::current_exception(), m_wallet->is_trusted_daemon());
  }
  catch (...)
  {
    LOG_ERROR("Unknown error");
    fail_msg_writer() << tr("未知错误");
  }

  return true;
}
//----------------------------------------------------------------------------------------------------
std::string get_tx_key_stream(crypto::secret_key tx_key, std::vector<crypto::secret_key> additional_tx_keys)
{
  ostringstream oss;
  oss << epee::string_tools::pod_to_hex(unwrap(unwrap(tx_key)));
  for (size_t i = 0; i < additional_tx_keys.size(); ++i)
    oss << epee::string_tools::pod_to_hex(unwrap(unwrap(additional_tx_keys[i])));
  return oss.str();
}

bool simple_wallet::get_tx_key(const std::vector<std::string> &args_)
{
  CHECK_IF_BACKGROUND_SYNCING("cannot get tx key");

  std::vector<std::string> local_args = args_;

  if (m_wallet->key_on_device() && m_wallet->get_account().get_device().get_type() != hw::device::TREZOR)
  {
    fail_msg_writer() << tr("硬件钱包不支持此命令");
    return true;
  }
  if(local_args.size() != 1) {
    PRINT_USAGE(USAGE_GET_TX_KEY);
    return true;
  }

  crypto::hash txid;
  if (!epee::string_tools::hex_to_pod(local_args[0], txid))
  {
    fail_msg_writer() << tr("解析交易 ID 失败");
    return true;
  }

  SCOPED_WALLET_UNLOCK();

  crypto::secret_key tx_key;
  std::vector<crypto::secret_key> additional_tx_keys;

  bool found_tx_key = m_wallet->get_tx_key(txid, tx_key, additional_tx_keys);
  if (found_tx_key)
  {
    std::string stream = get_tx_key_stream(tx_key, additional_tx_keys);
    success_msg_writer() << tr("交易密钥：") << stream;
    return true;
  }
  else
  {
    fail_msg_writer() << tr("未找到该交易 ID 对应的交易密钥");
    return true;
  }
}
//----------------------------------------------------------------------------------------------------
bool simple_wallet::set_tx_key(const std::vector<std::string> &args_)
{
  CHECK_IF_BACKGROUND_SYNCING("cannot set tx key");

  std::vector<std::string> local_args = args_;

  if(local_args.size() != 2 && local_args.size() != 3) {
    PRINT_USAGE(USAGE_SET_TX_KEY);
    return true;
  }

  boost::optional<cryptonote::account_public_address> single_destination_subaddress;
  if (local_args.size() > 1)
  {
    cryptonote::address_parse_info info;
    if (cryptonote::get_account_address_from_str_or_url(info, m_wallet->nettype(), local_args.back(), m_wallet->is_dns_enabled(), oa_prompter))
    {
      if (!info.is_subaddress)
      {
        fail_msg_writer() << tr("Last argument is an address, but not a subaddress");
        return true;
      }
      single_destination_subaddress = info.address;
      local_args.pop_back();
    }
  }

  crypto::hash txid;
  if (!epee::string_tools::hex_to_pod(local_args[0], txid))
  {
    fail_msg_writer() << tr("解析交易 ID 失败");
    return true;
  }

  crypto::secret_key tx_key;
  std::vector<crypto::secret_key> additional_tx_keys;
  try
  {
    if (!epee::string_tools::hex_to_pod(local_args[1].substr(0, 64), tx_key))
    {
      fail_msg_writer() << tr("failed to parse tx_key");
      return true;
    }
    while(true)
    {
      local_args[1] = local_args[1].substr(64);
      if (local_args[1].empty())
        break;
      additional_tx_keys.resize(additional_tx_keys.size() + 1);
      if (!epee::string_tools::hex_to_pod(local_args[1].substr(0, 64), additional_tx_keys.back()))
      {
        fail_msg_writer() << tr("failed to parse tx_key");
        return true;
      }
    }
  }
  catch (const std::out_of_range &e)
  {
    fail_msg_writer() << tr("failed to parse tx_key");
    return true;
  }

  LOCK_IDLE_SCOPE();

  try
  {
    m_wallet->set_tx_key(txid, tx_key, additional_tx_keys, single_destination_subaddress);
    success_msg_writer() << tr("交易密钥已成功保存。");
  }
  catch (const std::exception &e)
  {
    fail_msg_writer() << tr("保存交易密钥失败：") << e.what();
    if (!single_destination_subaddress)
      fail_msg_writer() << tr("可能是因为该转账发送到了子地址。如果是这种情况，请在最后提供子地址");
  }
  return true;
}
//----------------------------------------------------------------------------------------------------
bool simple_wallet::get_tx_proof(const std::vector<std::string> &args)
{
  CHECK_IF_BACKGROUND_SYNCING("cannot get tx proof");

  if (args.size() != 2 && args.size() != 3)
  {
    PRINT_USAGE(USAGE_GET_TX_PROOF);
    return true;
  }

  crypto::hash txid;
  if(!epee::string_tools::hex_to_pod(args[0], txid))
  {
    fail_msg_writer() << tr("解析交易 ID 失败");
    return true;
  }

  cryptonote::address_parse_info info;
  if(!cryptonote::get_account_address_from_str_or_url(info, m_wallet->nettype(), args[1], m_wallet->is_dns_enabled(), oa_prompter))
  {
    fail_msg_writer() << tr("解析地址失败");
    return true;
  }

  SCOPED_WALLET_UNLOCK();

  try
  {
    std::string sig_str = m_wallet->get_tx_proof(txid, info.address, info.is_subaddress, args.size() == 3 ? args[2] : "");
    const std::string filename = "monero_tx_proof";
    if (m_wallet->save_to_file(filename, sig_str, true))
      success_msg_writer() << tr("签名文件已保存到：") << filename;
    else
      fail_msg_writer() << tr("保存签名文件失败");
  }
  catch (const std::exception &e)
  {
    fail_msg_writer() << tr("error: ") << e.what();
  }
  return true;
}
//----------------------------------------------------------------------------------------------------
bool simple_wallet::check_tx_key(const std::vector<std::string> &args_)
{
  std::vector<std::string> local_args = args_;

  if(local_args.size() != 3) {
    PRINT_USAGE(USAGE_CHECK_TX_KEY);
    return true;
  }

  if (!try_connect_to_daemon())
    return true;

  if (!m_wallet)
  {
    fail_msg_writer() << tr("钱包为空");
    return true;
  }
  crypto::hash txid;
  if(!epee::string_tools::hex_to_pod(local_args[0], txid))
  {
    fail_msg_writer() << tr("解析交易 ID 失败");
    return true;
  }

  crypto::secret_key tx_key;
  std::vector<crypto::secret_key> additional_tx_keys;
  if(!epee::string_tools::hex_to_pod(local_args[1].substr(0, 64), tx_key))
  {
    fail_msg_writer() << tr("failed to parse tx key");
    return true;
  }
  local_args[1] = local_args[1].substr(64);
  while (!local_args[1].empty())
  {
    additional_tx_keys.resize(additional_tx_keys.size() + 1);
    if(!epee::string_tools::hex_to_pod(local_args[1].substr(0, 64), additional_tx_keys.back()))
    {
      fail_msg_writer() << tr("failed to parse tx key");
      return true;
    }
    local_args[1] = local_args[1].substr(64);
  }

  cryptonote::address_parse_info info;
  if(!cryptonote::get_account_address_from_str_or_url(info, m_wallet->nettype(), local_args[2], m_wallet->is_dns_enabled(), oa_prompter))
  {
    fail_msg_writer() << tr("解析地址失败");
    return true;
  }

  try
  {
    uint64_t received;
    bool in_pool;
    uint64_t confirmations;
    m_wallet->check_tx_key(txid, tx_key, additional_tx_keys, info.address, received, in_pool, confirmations);

    if (received > 0)
    {
      success_msg_writer() << get_account_address_as_str(m_wallet->nettype(), info.is_subaddress, info.address) << " " << tr("received") << " " << print_money(received) << " " << tr("in txid") << " " << txid;
      if (in_pool)
      {
        success_msg_writer() << tr("警告：此交易尚未被纳入区块链！");
      }
      else
      {
        if (confirmations != (uint64_t)-1)
        {
          success_msg_writer() << boost::format(tr("此交易已有 %u 个确认")) % confirmations;
        }
        else
        {
          success_msg_writer() << tr("警告：无法确定确认数！");
        }
      }
    }
    else
    {
      fail_msg_writer() << get_account_address_as_str(m_wallet->nettype(), info.is_subaddress, info.address) << " " << tr("该交易 ID 没有收到任何金额") << " " << txid;
    }
  }
  catch (const std::exception &e)
  {
    fail_msg_writer() << tr("error: ") << e.what();
  }
  return true;
}
//----------------------------------------------------------------------------------------------------
bool simple_wallet::check_tx_proof(const std::vector<std::string> &args)
{
  if(args.size() != 3 && args.size() != 4) {
    PRINT_USAGE(USAGE_CHECK_TX_PROOF);
    return true;
  }

  if (!try_connect_to_daemon())
    return true;

  // parse txid
  crypto::hash txid;
  if(!epee::string_tools::hex_to_pod(args[0], txid))
  {
    fail_msg_writer() << tr("解析交易 ID 失败");
    return true;
  }

  // parse address
  cryptonote::address_parse_info info;
  if(!cryptonote::get_account_address_from_str_or_url(info, m_wallet->nettype(), args[1], m_wallet->is_dns_enabled(), oa_prompter))
  {
    fail_msg_writer() << tr("解析地址失败");
    return true;
  }

  // read signature file
  std::string sig_str;
  if (!m_wallet->load_from_file(args[2], sig_str))
  {
    fail_msg_writer() << tr("加载签名文件失败");
    return true;
  }

  try
  {
    uint64_t received;
    bool in_pool;
    uint64_t confirmations;
    if (m_wallet->check_tx_proof(txid, info.address, info.is_subaddress, args.size() == 4 ? args[3] : "", sig_str, received, in_pool, confirmations))
    {
      success_msg_writer() << tr("签名有效");
      if (received > 0)
      {
        success_msg_writer() << get_account_address_as_str(m_wallet->nettype(), info.is_subaddress, info.address) << " " << tr("received") << " " << print_money(received) << " " << tr("in txid") << " " << txid;
        if (in_pool)
        {
          success_msg_writer() << tr("警告：此交易尚未被纳入区块链！");
        }
        else
        {
          if (confirmations != (uint64_t)-1)
          {
            success_msg_writer() << boost::format(tr("此交易已有 %u 个确认")) % confirmations;
          }
          else
          {
            success_msg_writer() << tr("警告：无法确定确认数！");
          }
        }
      }
      else
      {
        fail_msg_writer() << get_account_address_as_str(m_wallet->nettype(), info.is_subaddress, info.address) << " " << tr("该交易 ID 没有收到任何金额") << " " << txid;
      }
    }
    else
    {
      fail_msg_writer() << tr("签名无效");
    }
  }
  catch (const std::exception &e)
  {
    fail_msg_writer() << tr("error: ") << e.what();
  }
  return true;
}
//----------------------------------------------------------------------------------------------------
bool simple_wallet::get_spend_proof(const std::vector<std::string> &args)
{
  CHECK_IF_BACKGROUND_SYNCING("cannot get spend proof");
  if (m_wallet->key_on_device())
  {
    fail_msg_writer() << tr("硬件钱包不支持此命令");
    return true;
  }
  if(args.size() != 1 && args.size() != 2) {
    PRINT_USAGE(USAGE_GET_SPEND_PROOF);
    return true;
  }

  if (m_wallet->watch_only())
  {
    fail_msg_writer() << tr("仅观察钱包无法生成证明");
    return true;
  }

  crypto::hash txid;
  if (!epee::string_tools::hex_to_pod(args[0], txid))
  {
    fail_msg_writer() << tr("解析交易 ID 失败");
    return true;
  }

  if (!try_connect_to_daemon())
    return true;

  SCOPED_WALLET_UNLOCK();

  try
  {
    const std::string sig_str = m_wallet->get_spend_proof(txid, args.size() == 2 ? args[1] : "");
    const std::string filename = "monero_spend_proof";
    if (m_wallet->save_to_file(filename, sig_str, true))
      success_msg_writer() << tr("签名文件已保存到：") << filename;
    else
      fail_msg_writer() << tr("保存签名文件失败");
  }
  catch (const std::exception &e)
  {
    fail_msg_writer() << e.what();
  }
  return true;
}
//----------------------------------------------------------------------------------------------------
bool simple_wallet::check_spend_proof(const std::vector<std::string> &args)
{
  if(args.size() != 2 && args.size() != 3) {
    PRINT_USAGE(USAGE_CHECK_SPEND_PROOF);
    return true;
  }

  crypto::hash txid;
  if (!epee::string_tools::hex_to_pod(args[0], txid))
  {
    fail_msg_writer() << tr("解析交易 ID 失败");
    return true;
  }

  if (!try_connect_to_daemon())
    return true;

  std::string sig_str;
  if (!m_wallet->load_from_file(args[1], sig_str))
  {
    fail_msg_writer() << tr("加载签名文件失败");
    return true;
  }

  try
  {
    if (m_wallet->check_spend_proof(txid, args.size() == 3 ? args[2] : "", sig_str))
      success_msg_writer() << tr("签名有效");
    else
      fail_msg_writer() << tr("签名无效");
  }
  catch (const std::exception& e)
  {
    fail_msg_writer() << e.what();
  }
  return true;
}
//----------------------------------------------------------------------------------------------------
bool simple_wallet::get_reserve_proof(const std::vector<std::string> &args)
{
  CHECK_IF_BACKGROUND_SYNCING("cannot get reserve proof");
  if (m_wallet->key_on_device())
  {
    fail_msg_writer() << tr("硬件钱包不支持此命令");
    return true;
  }
  if(args.size() != 1 && args.size() != 2) {
    PRINT_USAGE(USAGE_GET_RESERVE_PROOF);
    return true;
  }

  if (m_wallet->watch_only() || m_wallet->get_multisig_status().multisig_is_active)
  {
    fail_msg_writer() << tr("只有完整钱包才能生成储备证明");
    return true;
  }

  boost::optional<std::pair<uint32_t, uint64_t>> account_minreserve;
  if (args[0] != "all")
  {
    account_minreserve = std::pair<uint32_t, uint64_t>();
    account_minreserve->first = m_current_subaddress_account;
    if (!cryptonote::parse_amount(account_minreserve->second, args[0]))
    {
      fail_msg_writer() << tr("金额错误：") << args[0];
      return true;
    }
  }

  if (!try_connect_to_daemon())
    return true;

  SCOPED_WALLET_UNLOCK();

  try
  {
    const std::string sig_str = m_wallet->get_reserve_proof(account_minreserve, args.size() == 2 ? args[1] : "");
    const std::string filename = "monero_reserve_proof";
    if (m_wallet->save_to_file(filename, sig_str, true))
      success_msg_writer() << tr("签名文件已保存到：") << filename;
    else
      fail_msg_writer() << tr("保存签名文件失败");
  }
  catch (const std::exception &e)
  {
    fail_msg_writer() << e.what();
  }
  return true;
}
//----------------------------------------------------------------------------------------------------
bool simple_wallet::check_reserve_proof(const std::vector<std::string> &args)
{
  if(args.size() != 2 && args.size() != 3) {
    PRINT_USAGE(USAGE_CHECK_RESERVE_PROOF);
    return true;
  }

  if (!try_connect_to_daemon())
    return true;

  cryptonote::address_parse_info info;
  if(!cryptonote::get_account_address_from_str_or_url(info, m_wallet->nettype(), args[0], m_wallet->is_dns_enabled(), oa_prompter))
  {
    fail_msg_writer() << tr("解析地址失败");
    return true;
  }
  if (info.is_subaddress)
  {
    fail_msg_writer() << tr("地址不能是子地址");
    return true;
  }

  std::string sig_str;
  if (!m_wallet->load_from_file(args[1], sig_str))
  {
    fail_msg_writer() << tr("加载签名文件失败");
    return true;
  }

  LOCK_IDLE_SCOPE();

  try
  {
    uint64_t total, spent;
    if (m_wallet->check_reserve_proof(info.address, args.size() == 3 ? args[2] : "", sig_str, total, spent))
    {
      success_msg_writer() << boost::format(tr("签名有效 -- total: %s, spent: %s, unspent: %s")) % print_money(total) % print_money(spent) % print_money(total - spent);
    }
    else
    {
      fail_msg_writer() << tr("签名无效");
    }
  }
  catch (const std::exception& e)
  {
    fail_msg_writer() << e.what();
  }
  return true;
}
//----------------------------------------------------------------------------------------------------
// mutates local_args as it parses and consumes arguments
bool simple_wallet::get_transfers(std::vector<std::string>& local_args, std::vector<transfer_view>& transfers)
{
  bool in = true;
  bool out = true;
  bool pending = true;
  bool failed = true;
  bool pool = true;
  bool coinbase = true;
  uint64_t min_height = 0;
  uint64_t max_height = (uint64_t)-1;

  // optional in/out selector
  if (local_args.size() > 0) {
    if (local_args[0] == "in" || local_args[0] == "incoming") {
      out = pending = failed = false;
      local_args.erase(local_args.begin());
    }
    else if (local_args[0] == "out" || local_args[0] == "outgoing") {
      in = pool = coinbase = false;
      local_args.erase(local_args.begin());
    }
    else if (local_args[0] == "pending") {
      in = out = failed = coinbase = false;
      local_args.erase(local_args.begin());
    }
    else if (local_args[0] == "failed") {
      in = out = pending = pool = coinbase = false;
      local_args.erase(local_args.begin());
    }
    else if (local_args[0] == "pool") {
      in = out = pending = failed = coinbase = false;
      local_args.erase(local_args.begin());
    }
    else if (local_args[0] == "coinbase") {
      in = out = pending = failed = pool = false;
      coinbase = true;
      local_args.erase(local_args.begin());
    }
    else if (local_args[0] == "all" || local_args[0] == "both") {
      local_args.erase(local_args.begin());
    }
  }

  // subaddr_index
  std::set<uint32_t> subaddr_indices;
  if (local_args.size() > 0 && local_args[0].substr(0, 6) == "index=")
  {
    if (!parse_subaddress_indices(local_args[0], subaddr_indices))
      return false;
    local_args.erase(local_args.begin());
  }

  // min height
  if (local_args.size() > 0 && local_args[0].find('=') == std::string::npos) {
    try {
      min_height = boost::lexical_cast<uint64_t>(local_args[0]);
    }
    catch (const boost::bad_lexical_cast &) {
      fail_msg_writer() << tr("无效的最小区块高度参数：") << " " << local_args[0];
      return false;
    }
    local_args.erase(local_args.begin());
  }

  // max height
  if (local_args.size() > 0 && local_args[0].find('=') == std::string::npos) {
    try {
      max_height = boost::lexical_cast<uint64_t>(local_args[0]);
    }
    catch (const boost::bad_lexical_cast &) {
      fail_msg_writer() << tr("无效的最大区块高度参数：") << " " << local_args[0];
      return false;
    }
    local_args.erase(local_args.begin());
  }

  const uint64_t last_block_height = m_wallet->get_blockchain_current_height();

  if (in || coinbase) {
    std::list<std::pair<crypto::hash, tools::wallet2::payment_details>> payments;
    m_wallet->get_payments(payments, min_height, max_height, m_current_subaddress_account, subaddr_indices);
    for (std::list<std::pair<crypto::hash, tools::wallet2::payment_details>>::const_iterator i = payments.begin(); i != payments.end(); ++i) {
      const tools::wallet2::payment_details &pd = i->second;
      if (!pd.m_coinbase && !in)
        continue;
      std::string payment_id = string_tools::pod_to_hex(i->first);
      if (payment_id.substr(16).find_first_not_of('0') == std::string::npos)
        payment_id = payment_id.substr(0,16);
      std::string note = m_wallet->get_tx_note(pd.m_tx_hash);
      std::string destination = m_wallet->get_subaddress_as_str({m_current_subaddress_account, pd.m_subaddr_index.minor});
      const std::string type = pd.m_coinbase ? tr("区块") : tr("in");
      const bool unlocked = m_wallet->is_transfer_unlocked(pd.m_unlock_time, pd.m_block_height);
      std::string locked_msg = "unlocked";
      if (!unlocked)
      {
        locked_msg = "locked";
        if (pd.m_unlock_time < CRYPTONOTE_MAX_BLOCK_NUMBER)
        {
          uint64_t bh = std::max(pd.m_unlock_time, pd.m_block_height + CRYPTONOTE_DEFAULT_TX_SPENDABLE_AGE);
          if (bh >= last_block_height)
            locked_msg = std::to_string(bh - last_block_height) + " blks";
        }
        else
        {
          const uint64_t adjusted_time = m_wallet->get_daemon_adjusted_time();
          uint64_t threshold = adjusted_time + (m_wallet->use_fork_rules(2, 0) ? CRYPTONOTE_LOCKED_TX_ALLOWED_DELTA_SECONDS_V2 : CRYPTONOTE_LOCKED_TX_ALLOWED_DELTA_SECONDS_V1);
          if (threshold < pd.m_unlock_time)
            locked_msg = tools::get_human_readable_timespan(std::chrono::seconds(pd.m_unlock_time - threshold));
        }
      }
      transfers.push_back({
        type,
        pd.m_block_height,
        pd.m_timestamp,
        type,
        true,
        pd.m_amount,
        pd.m_tx_hash,
        payment_id,
        0,
        {{destination, pd.m_amount}},
        {pd.m_subaddr_index.minor},
        note,
        locked_msg
      });
    }
  }

  if (out) {
    std::list<std::pair<crypto::hash, tools::wallet2::confirmed_transfer_details>> payments;
    m_wallet->get_payments_out(payments, min_height, max_height, m_current_subaddress_account, subaddr_indices);
    for (std::list<std::pair<crypto::hash, tools::wallet2::confirmed_transfer_details>>::const_iterator i = payments.begin(); i != payments.end(); ++i) {
      const tools::wallet2::confirmed_transfer_details &pd = i->second;
      uint64_t change = pd.m_change == (uint64_t)-1 ? 0 : pd.m_change; // change may not be known
      uint64_t fee = pd.m_amount_in - pd.m_amount_out;
      std::vector<std::pair<std::string, uint64_t>> destinations;
      for (const auto &d: pd.m_dests) {
        destinations.push_back({d.address(m_wallet->nettype(), pd.m_payment_id), d.amount});
      }
      std::string payment_id = string_tools::pod_to_hex(i->second.m_payment_id);
      if (payment_id.substr(16).find_first_not_of('0') == std::string::npos)
        payment_id = payment_id.substr(0,16);
      std::string note = m_wallet->get_tx_note(i->first);
      transfers.push_back({
        "out",
        pd.m_block_height,
        pd.m_timestamp,
        "out",
        true,
        pd.m_amount_in - change - fee,
        i->first,
        payment_id,
        fee,
        destinations,
        pd.m_subaddr_indices,
        note,
        "-"
      });
    }
  }

  if (pool) {
    try
    {
      m_in_manual_refresh.store(true, std::memory_order_relaxed);
      const epee::scope_guard scope_exit_handler([&](){m_in_manual_refresh.store(false, std::memory_order_relaxed);});

      std::vector<std::tuple<cryptonote::transaction, crypto::hash, bool>> process_txs;
      m_wallet->update_pool_state(process_txs);
      if (!process_txs.empty())
        m_wallet->process_pool_state(process_txs);

      std::list<std::pair<crypto::hash, tools::wallet2::pool_payment_details>> payments;
      m_wallet->get_unconfirmed_payments(payments, m_current_subaddress_account, subaddr_indices);
      for (std::list<std::pair<crypto::hash, tools::wallet2::pool_payment_details>>::const_iterator i = payments.begin(); i != payments.end(); ++i) {
        const tools::wallet2::payment_details &pd = i->second.m_pd;
        std::string payment_id = string_tools::pod_to_hex(i->first);
        if (payment_id.substr(16).find_first_not_of('0') == std::string::npos)
          payment_id = payment_id.substr(0,16);
        std::string note = m_wallet->get_tx_note(pd.m_tx_hash);
        std::string destination = m_wallet->get_subaddress_as_str({m_current_subaddress_account, pd.m_subaddr_index.minor});
        std::string double_spend_note;
        if (i->second.m_double_spend_seen)
          double_spend_note = tr("[网络检测到双花：此交易可能会被打包，也可能不会] ");
        transfers.push_back({
          "pool",
          "pool",
          pd.m_timestamp,
          "in",
          false,
          pd.m_amount,
          pd.m_tx_hash,
          payment_id,
          0,
          {{destination, pd.m_amount}},
          {pd.m_subaddr_index.minor},
          note + double_spend_note,
          "locked"
        });
      }
    }
    catch (const std::exception& e)
    {
      fail_msg_writer() << "Failed to get pool state:" << e.what();
    }
  }

  // print unconfirmed last
  if (pending || failed) {
    std::list<std::pair<crypto::hash, tools::wallet2::unconfirmed_transfer_details>> upayments;
    m_wallet->get_unconfirmed_payments_out(upayments, m_current_subaddress_account, subaddr_indices);
    for (std::list<std::pair<crypto::hash, tools::wallet2::unconfirmed_transfer_details>>::const_iterator i = upayments.begin(); i != upayments.end(); ++i) {
      const tools::wallet2::unconfirmed_transfer_details &pd = i->second;
      uint64_t amount = pd.m_amount_in;
      uint64_t fee = amount - pd.m_amount_out;
      std::vector<std::pair<std::string, uint64_t>> destinations;
      for (const auto &d: pd.m_dests) {
        destinations.push_back({d.address(m_wallet->nettype(), pd.m_payment_id), d.amount});
      }
      std::string payment_id = string_tools::pod_to_hex(i->second.m_payment_id);
      if (payment_id.substr(16).find_first_not_of('0') == std::string::npos)
        payment_id = payment_id.substr(0,16);
      std::string note = m_wallet->get_tx_note(i->first);
      bool is_failed = pd.m_state == tools::wallet2::unconfirmed_transfer_details::failed;
      if ((failed && is_failed) || (!is_failed && pending)) {
        transfers.push_back({
          (is_failed ? "failed" : "pending"),
          (is_failed ? "failed" : "pending"),
          pd.m_timestamp,
          "out",
          false,
          amount - pd.m_change - fee,
          i->first,
          payment_id,
          fee,
          destinations,
          pd.m_subaddr_indices,
          note,
          "-"
        });
      }
    }
  }
  // sort by block, then by timestamp (unconfirmed last)
  std::sort(transfers.begin(), transfers.end(), [](const transfer_view& a, const transfer_view& b) -> bool {
    if (a.confirmed && !b.confirmed)
      return true;
    if (a.block == b.block)
      return a.timestamp < b.timestamp;
    return a.block < b.block;
  });

  return true;
}
//----------------------------------------------------------------------------------------------------
bool simple_wallet::show_transfers(const std::vector<std::string> &args_)
{
  std::vector<std::string> local_args = args_;

  if(local_args.size() > 4) {
    fail_msg_writer() << tr("usage: show_transfers [in|out|all|pending|failed|pool|coinbase] [index=<N1>[,<N2>,...]] [<min_height> [<max_height>]]");
    return true;
  }

  LOCK_IDLE_SCOPE();

  std::vector<transfer_view> all_transfers;

  if (!get_transfers(local_args, all_transfers))
    return true;

  PAUSE_READLINE();

  auto formatter = boost::format("%8.8s %6.6s %8.8s %25.25s %20.20s %64.64s %16.16s %14.14s %s %s - %s");
  message_writer(console_color_default, false) << formatter
  % "Block"
  % "In/Out"
  % "Locked?"
  % "Timestamp"
  % "Amount"
  % "Tx Hash"
  % "Tx Payment ID"
  % "Tx Fee"
  % "Destination(s)"
  % "Index"
  % "Tx Note";

  formatter = boost::format("%8.8llu %6.6s %8.8s %25.25s %20.20s %64.64s %16.16s %14.14s %s %s - %s");

  for (const auto& transfer : all_transfers)
  {
    const auto color = transfer.type == "failed" ? console_color_red : transfer.confirmed ? ((transfer.direction == "in" || transfer.direction == "block") ? console_color_green : console_color_magenta) : console_color_default;

    std::string destinations = "-";
    if (!transfer.outputs.empty())
    {
      destinations = "";
      for (const auto& output : transfer.outputs)
      {
        if (!destinations.empty())
          destinations += ", ";
        destinations += (transfer.direction == "in" ? output.first.substr(0, 6) : output.first) + ":" + print_money(output.second);
      }
    }

    message_writer(color, false) << formatter
      % transfer.block
      % transfer.direction
      % transfer.unlocked
      % tools::get_human_readable_timestamp(transfer.timestamp)
      % print_money(transfer.amount)
      % string_tools::pod_to_hex(transfer.hash)
      % transfer.payment_id
      % print_money(transfer.fee)
      % destinations
      % boost::algorithm::join(transfer.index | boost::adaptors::transformed([](uint32_t i) { return std::to_string(i); }), ", ")
      % transfer.note;
  }

  return true;
}
//----------------------------------------------------------------------------------------------------
bool simple_wallet::export_transfers(const std::vector<std::string>& args_)
{
  std::vector<std::string> local_args = args_;

  if(local_args.size() > 6) {
    fail_msg_writer() << tr("usage: export_transfers [in|out|all|pending|failed|pool|coinbase] [index=<N1>[,<N2>,...]] [<min_height> [<max_height>]] [output=<path>] [option=<with_keys>]");
    return true;
  }

  std::vector<transfer_view> all_transfers;

  // might consumes arguments in local_args
  if (!get_transfers(local_args, all_transfers))
    return true;

  // output filename
  std::string filename = (boost::format("output%u.csv") % m_current_subaddress_account).str();
  if (local_args.size() > 0 && local_args[0].substr(0, 7) == "output=")
  {
    filename = local_args[0].substr(7, -1);
    local_args.erase(local_args.begin());
  }
  // check for export with tx keys
  bool export_keys = false;
  if (local_args.size() > 0 && local_args[0].substr(0, 7) == "option=")
  {
    export_keys = local_args[0].substr(7, -1) == "with_keys";
    local_args.erase(local_args.begin());
  }
  if (export_keys)
  {
    if (m_wallet->key_on_device() && m_wallet->get_account().get_device().get_type() != hw::device::TREZOR)
    {
      fail_msg_writer() << tr("硬件钱包不支持此命令");
      return true;
    }
    SCOPED_WALLET_UNLOCK();
  } else 
  {
    LOCK_IDLE_SCOPE();
  }

  std::ofstream file(filename);
  if(file.fail()) {
    fail_msg_writer() << boost::format(tr("无法打开 %s 进行写入")) % filename;
    return true;
  }

  // header
  file <<
      boost::format("%8.8s,%9.9s,%8.8s,%25.25s,%20.20s,%20.20s,%64.64s,%16.16s,%14.14s,%106.106s,%20.20s,%s,%s,%s") %
      tr("区块") % tr("方向") % tr("unlocked") % tr("时间戳") % tr("交易金额") % tr("余额变化") % tr("哈希") % tr("支付 ID") % tr("手续费") % tr("目标地址") % tr("目标金额") % tr("索引") % tr("备注") % tr("交易密钥")
      << std::endl;

  uint64_t running_balance = 0;
  auto formatter = boost::format("%8.8llu,%9.9s,%8.8s,%25.25s,%20.20s,%20.20s,%64.64s,%16.16s,%14.14s,%106.106s,%20.20s,\"%s\",\"%s\",%s");

  for (const auto& transfer : all_transfers)
  {
    // ignore unconfirmed transfers in running balance
    if (transfer.confirmed)
    {
      if (transfer.direction == "in" || transfer.direction == "block")
        running_balance += transfer.amount;
      else
        running_balance -= transfer.amount + transfer.fee;
    }

    std::string key_string;
    if (export_keys)
    {
      crypto::secret_key tx_key;
      std::vector<crypto::secret_key> additional_tx_keys;
      if (m_wallet->get_tx_key(transfer.hash, tx_key, additional_tx_keys))
        key_string = get_tx_key_stream(tx_key, additional_tx_keys);
    }

    std::string note = transfer.note;
    boost::replace_all(note, "\"", "\"\"");

    file << formatter
      % transfer.block
      % transfer.direction
      % transfer.unlocked
      % tools::get_human_readable_timestamp(transfer.timestamp)
      % print_money(transfer.amount)
      % print_money(running_balance)
      % string_tools::pod_to_hex(transfer.hash)
      % transfer.payment_id
      % print_money(transfer.fee)
      % (transfer.outputs.size() ? transfer.outputs[0].first : "-")
      % (transfer.outputs.size() ? print_money(transfer.outputs[0].second) : "")
      % boost::algorithm::join(transfer.index | boost::adaptors::transformed([](uint32_t i) { return std::to_string(i); }), ", ")
      % note
      % key_string
      << std::endl;

    for (size_t i = 1; i < transfer.outputs.size(); ++i)
    {
      file << formatter
        % ""
        % ""
        % ""
        % ""
        % ""
        % ""
        % ""
        % ""
        % ""
        % transfer.outputs[i].first
        % print_money(transfer.outputs[i].second)
        % ""
        % ""
        % ""
        << std::endl;
    }
  }
  file.close();

  if(file.fail()) {
    fail_msg_writer() << tr("导出 CSV 失败：") << filename;
  } else {
    success_msg_writer() << tr("CSV 已导出到：") << filename;
  }

  return true;
}
//----------------------------------------------------------------------------------------------------
bool simple_wallet::unspent_outputs(const std::vector<std::string> &args_)
{
  if(args_.size() > 3)
  {
    PRINT_USAGE(USAGE_UNSPENT_OUTPUTS);
    return true;
  }
  auto local_args = args_;

  std::set<uint32_t> subaddr_indices;
  if (local_args.size() > 0 && local_args[0].substr(0, 6) == "index=")
  {
    if (!parse_subaddress_indices(local_args[0], subaddr_indices))
      return true;
    local_args.erase(local_args.begin());
  }

  uint64_t min_amount = 0;
  uint64_t max_amount = std::numeric_limits<uint64_t>::max();
  if (local_args.size() > 0)
  {
    if (!cryptonote::parse_amount(min_amount, local_args[0]))
    {
      fail_msg_writer() << tr("金额错误：") << local_args[0];
      return true;
    }
    local_args.erase(local_args.begin());
    if (local_args.size() > 0)
    {
      if (!cryptonote::parse_amount(max_amount, local_args[0]))
      {
        fail_msg_writer() << tr("金额错误：") << local_args[0];
        return true;
      }
      local_args.erase(local_args.begin());
    }
    if (min_amount > max_amount)
    {
      fail_msg_writer() << tr("<min_amount> 应小于 <max_amount>");
      return true;
    }
  }
  tools::wallet2::transfer_container transfers;
  m_wallet->get_transfers(transfers);
  std::map<uint64_t, tools::wallet2::transfer_container> amount_to_tds;
  uint64_t min_height = std::numeric_limits<uint64_t>::max();
  uint64_t max_height = 0;
  uint64_t found_min_amount = std::numeric_limits<uint64_t>::max();
  uint64_t found_max_amount = 0;
  uint64_t found_sum_amount = 0;
  uint64_t count = 0;
  for (const auto& td : transfers)
  {
    uint64_t amount = td.amount();
    if (td.m_spent || amount < min_amount || amount > max_amount || td.m_subaddr_index.major != m_current_subaddress_account || (subaddr_indices.count(td.m_subaddr_index.minor) == 0 && !subaddr_indices.empty()))
      continue;
    amount_to_tds[amount].push_back(td);
    if (min_height > td.m_block_height) min_height = td.m_block_height;
    if (max_height < td.m_block_height) max_height = td.m_block_height;
    if (found_min_amount > amount) found_min_amount = amount;
    if (found_max_amount < amount) found_max_amount = amount;
    found_sum_amount += amount;
    ++count;
  }
  if (amount_to_tds.empty())
  {
    success_msg_writer() << tr("指定地址没有未花费输出");
    return true;
  }
  for (const auto& amount_tds : amount_to_tds)
  {
    auto& tds = amount_tds.second;
    success_msg_writer() << tr("\nAmount: ") << print_money(amount_tds.first) << tr(", number of keys: ") << tds.size();
    for (size_t i = 0; i < tds.size(); )
    {
      std::ostringstream oss;
      for (size_t j = 0; j < 8 && i < tds.size(); ++i, ++j)
        oss << tds[i].m_block_height << tr(" ");
      success_msg_writer() << oss.str();
    }
  }
  success_msg_writer()
    << tr("\nMin block height: ") << min_height
    << tr("\nMax block height: ") << max_height
    << tr("\nMin amount found: ") << print_money(found_min_amount)
    << tr("\nMax amount found: ") << print_money(found_max_amount)
    << tr("\nSum amount found: ") << print_money(found_sum_amount)
    << tr("\nTotal count: ") << count;
  const size_t histogram_height = 10;
  const size_t histogram_width  = 50;
  double bin_size = (max_height - min_height + 1.0) / histogram_width;
  size_t max_bin_count = 0;
  std::vector<size_t> histogram(histogram_width, 0);
  for (const auto& amount_tds : amount_to_tds)
  {
    for (auto& td : amount_tds.second)
    {
      uint64_t bin_index = (td.m_block_height - min_height + 1) / bin_size;
      if (bin_index >= histogram_width)
        bin_index = histogram_width - 1;
      histogram[bin_index]++;
      if (max_bin_count < histogram[bin_index])
        max_bin_count = histogram[bin_index];
    }
  }
  for (size_t x = 0; x < histogram_width; ++x)
  {
    double bin_count = histogram[x];
    if (max_bin_count > histogram_height)
      bin_count *= histogram_height / (double)max_bin_count;
    if (histogram[x] > 0 && bin_count < 1.0)
      bin_count = 1.0;
    histogram[x] = bin_count;
  }
  std::vector<std::string> histogram_line(histogram_height, std::string(histogram_width, ' '));
  for (size_t y = 0; y < histogram_height; ++y)
  {
    for (size_t x = 0; x < histogram_width; ++x)
    {
      if (y < histogram[x])
        histogram_line[y][x] = '*';
    }
  }
  double count_per_star = max_bin_count / (double)histogram_height;
  if (count_per_star < 1)
    count_per_star = 1;
  success_msg_writer()
    << tr("\nBin size: ") << bin_size
    << tr("\nOutputs per *: ") << count_per_star;
  ostringstream histogram_str;
  histogram_str << tr("count\n  ^\n");
  for (size_t y = histogram_height; y > 0; --y)
    histogram_str << tr("  |") << histogram_line[y - 1] << tr("|\n");
  histogram_str
    << tr("  +") << std::string(histogram_width, '-') << tr("+--> block height\n")
    << tr("   ^") << std::string(histogram_width - 2, ' ') << tr("^\n")
    << tr("  ") << min_height << std::string(histogram_width - 8, ' ') << max_height;
  success_msg_writer() << histogram_str.str();
  return true;
}
//----------------------------------------------------------------------------------------------------
bool simple_wallet::rescan_blockchain(const std::vector<std::string> &args_)
{
  CHECK_IF_BACKGROUND_SYNCING("cannot rescan");

  uint64_t start_height = 0;
  ResetType reset_type = ResetSoft;

  if (!args_.empty())
  {
    if (args_[0] == "hard")
    {
      reset_type = ResetHard;
    }
    else if (args_[0] == "soft")
    {
      reset_type = ResetSoft;
    }
    else if (args_[0] == "keep_ki")
    {
      reset_type = ResetSoftKeepKI;
    }
    else
    {
      PRINT_USAGE(USAGE_RESCAN_BC);
      return true;
    }

    if (args_.size() > 1)
    {
      try
      {
        start_height = boost::lexical_cast<uint64_t>( args_[1] );
      }
      catch(const boost::bad_lexical_cast &)
      {
        start_height = 0;
      }
    }
  }

  if (reset_type == ResetHard)
  {
    message_writer() << tr("警告：此操作将丢失无法从区块链恢复的信息。");
    message_writer() << tr("包括目标地址、交易私钥、交易备注等信息");
    std::string confirm = input_line(tr("仍要重新扫描吗？"), true);
    if(!std::cin.eof())
    {
      if (!command_line::is_yes(confirm))
        return true;
    }
  }

  const uint64_t wallet_from_height = m_wallet->get_refresh_from_block_height();
  if (start_height > wallet_from_height)
  {
    message_writer() << tr("警告：指定的恢复高度高于钱包恢复高度：") << wallet_from_height;
    std::string confirm = input_line(tr("仍要重新扫描吗？"), true);
    if(!std::cin.eof())
    {
      if (!command_line::is_yes(confirm))
        return true;
    }
  }

  m_in_manual_refresh.store(true, std::memory_order_relaxed);
  const epee::scope_guard scope_exit_handler([&](){m_in_manual_refresh.store(false, std::memory_order_relaxed);});
  return refresh_main(start_height, reset_type, true);
}
//----------------------------------------------------------------------------------------------------
void simple_wallet::check_for_messages()
{
  try
  {
    std::vector<mms::message> new_messages;
    bool new_message = get_message_store().check_for_messages(get_multisig_wallet_state(), new_messages);
    if (new_message)
    {
      message_writer(console_color_magenta, true) << tr("MMS 收到新消息");
      list_mms_messages(new_messages);
      m_cmd_binder.print_prompt();
    }
  }
  catch(...) {}
}
//----------------------------------------------------------------------------------------------------
void simple_wallet::wallet_idle_thread()
{
  const boost::posix_time::ptime start_time = boost::posix_time::microsec_clock::universal_time();
  while (true)
  {
    boost::unique_lock<boost::mutex> lock(m_idle_mutex);
    if (!m_idle_run.load(std::memory_order_relaxed))
      break;

    // if another thread was busy (ie, a foreground refresh thread), we'll end up here at
    // some random time that's not what we slept for, so we should not call refresh now
    // or we'll be leaking that fact through timing
    const boost::posix_time::ptime now0 = boost::posix_time::microsec_clock::universal_time();
    const uint64_t dt_actual = (now0 - start_time).total_microseconds() % 1000000;
#ifdef _WIN32
    static const uint64_t threshold = 10000;
#else
    static const uint64_t threshold = 2000;
#endif
    if (dt_actual < threshold) // if less than a threshold... would a very slow machine always miss it ?
    {
#ifndef _WIN32
      m_inactivity_checker.do_call(boost::bind(&simple_wallet::check_inactivity, this));
#endif
      m_refresh_checker.do_call(boost::bind(&simple_wallet::check_refresh, this));
      m_mms_checker.do_call(boost::bind(&simple_wallet::check_mms, this));

      if (!m_idle_run.load(std::memory_order_relaxed))
        break;
    }

    // aim for the next multiple of 1 second
    const boost::posix_time::ptime now = boost::posix_time::microsec_clock::universal_time();
    const auto dt = (now - start_time).total_microseconds();
    const auto wait = 1000000 - dt % 1000000;
    m_idle_cond.wait_for(lock, boost::chrono::microseconds(wait));
  }
}
//----------------------------------------------------------------------------------------------------
bool simple_wallet::check_inactivity()
{
    // inactivity lock
    if (!m_locked && !m_in_command)
    {
      const uint32_t seconds = m_wallet->inactivity_lock_timeout();
      if (seconds > 0 && time(NULL) - m_last_activity_time > seconds)
      {
        m_locked = true;
        m_cmd_binder.cancel_input();
      }
    }
    return true;
}
//----------------------------------------------------------------------------------------------------
bool simple_wallet::check_refresh()
{
    // auto refresh
    if (m_auto_refresh_enabled)
    {
      m_auto_refresh_refreshing = true;
      try
      {
        uint64_t fetched_blocks;
        bool received_money;
        if (try_connect_to_daemon(true))
          m_wallet->refresh(m_wallet->is_trusted_daemon(), 0, fetched_blocks, received_money, false); // don't check the pool in background mode
      }
      catch(...) {}
      m_auto_refresh_refreshing = false;
    }
    return true;
}
//----------------------------------------------------------------------------------------------------
bool simple_wallet::check_mms()
{
    // Check for new MMS messages;
    // For simplicity auto message check is ALSO controlled by "m_auto_refresh_enabled" and has no
    // separate thread either; thread syncing is tricky enough with only this one idle thread here
    if (m_auto_refresh_enabled && get_message_store().get_active())
    {
      check_for_messages();
    }
    return true;
}
//----------------------------------------------------------------------------------------------------
std::string simple_wallet::get_prompt() const
{
  if (m_locked)
    return std::string("[") + tr("因长时间无操作已锁定") + "]";
  std::string addr_start = m_wallet->get_subaddress_as_str({m_current_subaddress_account, 0}).substr(0, 6);
  std::string prompt = std::string("[") + tr("钱包") + " " + addr_start;
  if (!m_wallet->check_connection(NULL))
    prompt += tr("（无守护进程）");
  else if (!m_wallet->is_synced())
    prompt += tr("（未同步）");
  prompt += "]: ";
  return prompt;
}
//----------------------------------------------------------------------------------------------------
bool simple_wallet::run()
{
  // check and display warning, but go on anyway
  try_connect_to_daemon();

  refresh_main(0, ResetNone, true);

  m_auto_refresh_enabled = !m_wallet->is_offline() && m_wallet->auto_refresh();
  m_idle_thread = boost::thread([&]{wallet_idle_thread();});

  message_writer(console_color_green, false) << "Background refresh thread started";
  return m_cmd_binder.run_handling([this](){return get_prompt();}, "");
}
//----------------------------------------------------------------------------------------------------
void simple_wallet::stop()
{
  m_cmd_binder.stop_handling();
}
//----------------------------------------------------------------------------------------------------
bool simple_wallet::account(const std::vector<std::string> &args/* = std::vector<std::string>()*/)
{
  // Usage:
  //   account
  //   account new <label text with white spaces allowed>
  //   account switch <index>
  //   account label <index> <label text with white spaces allowed>
  //   account tag <tag_name> <account_index_1> [<account_index_2> ...]
  //   account untag <account_index_1> [<account_index_2> ...]
  //   account tag_description <tag_name> <description>

  if (args.empty())
  {
    // print all the existing accounts
    LOCK_IDLE_SCOPE();
    print_accounts();
    return true;
  }

  std::vector<std::string> local_args = args;
  std::string command = local_args[0];
  local_args.erase(local_args.begin());
  if (command == "new")
  {
    // create a new account and switch to it
    CHECK_IF_BACKGROUND_SYNCING("cannot create new account");
    std::string label = boost::join(local_args, " ");
    if (label.empty())
      label = tr("（未命名账户）");
    m_wallet->add_subaddress_account(label);
    m_current_subaddress_account = m_wallet->get_num_subaddress_accounts() - 1;
    // update_prompt();
    LOCK_IDLE_SCOPE();
    print_accounts();
  }
  else if (command == "switch" && local_args.size() == 1)
  {
    // switch to the specified account
    uint32_t index_major;
    if (!epee::string_tools::get_xtype_from_string(index_major, local_args[0]))
    {
      fail_msg_writer() << tr("解析索引失败：") << local_args[0];
      return true;
    }
    if (index_major >= m_wallet->get_num_subaddress_accounts())
    {
      fail_msg_writer() << tr("specify an index between 0 and ") << (m_wallet->get_num_subaddress_accounts() - 1);
      return true;
    }
    m_current_subaddress_account = index_major;
    // update_prompt();
    show_balance();
  }
  else if (command == "label" && local_args.size() >= 1)
  {
    // set label of the specified account
    CHECK_IF_BACKGROUND_SYNCING("cannot modify account");
    uint32_t index_major;
    if (!epee::string_tools::get_xtype_from_string(index_major, local_args[0]))
    {
      fail_msg_writer() << tr("解析索引失败：") << local_args[0];
      return true;
    }
    local_args.erase(local_args.begin());
    std::string label = boost::join(local_args, " ");
    try
    {
      m_wallet->set_subaddress_label({index_major, 0}, label);
      LOCK_IDLE_SCOPE();
      print_accounts();
    }
    catch (const std::exception& e)
    {
      fail_msg_writer() << e.what();
    }
  }
  else if (command == "tag" && local_args.size() >= 2)
  {
    CHECK_IF_BACKGROUND_SYNCING("cannot modify account");
    const std::string tag = local_args[0];
    std::set<uint32_t> account_indices;
    for (size_t i = 1; i < local_args.size(); ++i)
    {
      uint32_t account_index;
      if (!epee::string_tools::get_xtype_from_string(account_index, local_args[i]))
      {
        fail_msg_writer() << tr("解析索引失败：") << local_args[i];
        return true;
      }
      account_indices.insert(account_index);
    }
    try
    {
      m_wallet->set_account_tag(account_indices, tag);
      print_accounts(tag);
    }
    catch (const std::exception& e)
    {
      fail_msg_writer() << e.what();
    }
  }
  else if (command == "untag" && local_args.size() >= 1)
  {
    CHECK_IF_BACKGROUND_SYNCING("cannot modify account");
    std::set<uint32_t> account_indices;
    for (size_t i = 0; i < local_args.size(); ++i)
    {
      uint32_t account_index;
      if (!epee::string_tools::get_xtype_from_string(account_index, local_args[i]))
      {
        fail_msg_writer() << tr("解析索引失败：") << local_args[i];
        return true;
      }
      account_indices.insert(account_index);
    }
    try
    {
      m_wallet->set_account_tag(account_indices, "");
      print_accounts();
    }
    catch (const std::exception& e)
    {
      fail_msg_writer() << e.what();
    }
  }
  else if (command == "tag_description" && local_args.size() >= 1)
  {
    CHECK_IF_BACKGROUND_SYNCING("cannot modify account");
    const std::string tag = local_args[0];
    std::string description;
    if (local_args.size() > 1)
    {
      local_args.erase(local_args.begin());
      description = boost::join(local_args, " ");
    }
    try
    {
      m_wallet->set_account_tag_description(tag, description);
      print_accounts(tag);
    }
    catch (const std::exception& e)
    {
      fail_msg_writer() << e.what();
    }
  }
  else
  {
    PRINT_USAGE(USAGE_ACCOUNT);
  }
  return true;
}
//----------------------------------------------------------------------------------------------------
void simple_wallet::print_accounts()
{
  const std::pair<std::map<std::string, std::string>, std::vector<std::string>>& account_tags = m_wallet->get_account_tags();
  size_t num_untagged_accounts = m_wallet->get_num_subaddress_accounts();
  for (const std::pair<const std::string, std::string>& p : account_tags.first)
  {
    const std::string& tag = p.first;
    print_accounts(tag);
    num_untagged_accounts -= std::count(account_tags.second.begin(), account_tags.second.end(), tag);
    success_msg_writer() << "";
  }

  if (num_untagged_accounts > 0)
    print_accounts("");

  if (num_untagged_accounts < m_wallet->get_num_subaddress_accounts())
    success_msg_writer() << tr("\nGrand total:\n  Balance: ") << print_money(m_wallet->balance_all(false)) << tr(", unlocked balance: ") << print_money(m_wallet->unlocked_balance_all(false));
}
//----------------------------------------------------------------------------------------------------
void simple_wallet::print_accounts(const std::string& tag)
{
  const std::pair<std::map<std::string, std::string>, std::vector<std::string>>& account_tags = m_wallet->get_account_tags();
  if (tag.empty())
  {
    success_msg_writer() << tr("未标记账户：");
  }
  else
  {
    if (account_tags.first.count(tag) == 0)
    {
      fail_msg_writer() << boost::format(tr("标签 %s 尚未注册。")) % tag;
      return;
    }
    success_msg_writer() << tr("使用此标签的账户：") << tag;
    success_msg_writer() << tr("标签说明：") << account_tags.first.find(tag)->second;
  }
  success_msg_writer() << boost::format("  %15s %21s %21s %21s") % tr("账户") % tr("余额") % tr("可用余额") % tr("标签");
  uint64_t total_balance = 0, total_unlocked_balance = 0;
  for (uint32_t account_index = 0; account_index < m_wallet->get_num_subaddress_accounts(); ++account_index)
  {
    if (account_tags.second[account_index] != tag)
      continue;
    success_msg_writer() << boost::format(tr(" %c%8u %6s %21s %21s %21s"))
      % (m_current_subaddress_account == account_index ? '*' : ' ')
      % account_index
      % m_wallet->get_subaddress_as_str({account_index, 0}).substr(0, 6)
      % print_money(m_wallet->balance(account_index, false))
      % print_money(m_wallet->unlocked_balance(account_index, false))
      % m_wallet->get_subaddress_label({account_index, 0});
    total_balance += m_wallet->balance(account_index, false);
    total_unlocked_balance += m_wallet->unlocked_balance(account_index, false);
  }
  success_msg_writer() << tr("------------------------------------------------------------------------------------");
  success_msg_writer() << boost::format(tr("%15s   %21s %21s")) % "Total" % print_money(total_balance) % print_money(total_unlocked_balance);
}
//----------------------------------------------------------------------------------------------------
bool simple_wallet::print_address(const std::vector<std::string> &args/* = std::vector<std::string>()*/)
{
  // Usage:
  //  address
  //  address new <label text with white spaces allowed>
  //  address all
  //  address <index_min> [<index_max>]
  //  address label <index> <label text with white spaces allowed>
  //  address device [<index>]

  std::vector<std::string> local_args = args;
  tools::wallet2::transfer_container transfers;
  m_wallet->get_transfers(transfers);

  auto print_address_sub = [this, &transfers](uint32_t index)
  {
    bool used = std::find_if(
      transfers.begin(), transfers.end(),
      [this, &index](const tools::wallet2::transfer_details& td) {
        return td.m_subaddr_index == cryptonote::subaddress_index{ m_current_subaddress_account, index };
      }) != transfers.end();
    success_msg_writer() << index << "  " << m_wallet->get_subaddress_as_str({m_current_subaddress_account, index}) << "  " << (index == 0 ? tr("主地址") : m_wallet->get_subaddress_label({m_current_subaddress_account, index})) << " " << (used ? tr("（已使用）") : "");
  };

  uint32_t index = 0;
  if (local_args.empty())
  {
    print_address_sub(index);
  }
  else if (local_args.size() == 1 && local_args[0] == "all")
  {
    local_args.erase(local_args.begin());
    for (; index < m_wallet->get_num_subaddresses(m_current_subaddress_account); ++index)
      print_address_sub(index);
  }
  else if (local_args[0] == "new")
  {
    CHECK_IF_BACKGROUND_SYNCING("cannot add address");
    local_args.erase(local_args.begin());
    std::string label;
    if (local_args.size() > 0)
      label = boost::join(local_args, " ");
    if (label.empty())
      label = tr("（未命名地址）");
    m_wallet->add_subaddress(m_current_subaddress_account, label);
    print_address_sub(m_wallet->get_num_subaddresses(m_current_subaddress_account) - 1);
    m_wallet->device_show_address(m_current_subaddress_account, m_wallet->get_num_subaddresses(m_current_subaddress_account) - 1, boost::none);
  }
  else if (local_args[0] == "mnew")
  {
    CHECK_IF_BACKGROUND_SYNCING("cannot add addresses");
    local_args.erase(local_args.begin());
    if (local_args.size() != 1)
    {
      fail_msg_writer() << tr("新地址数量必须只提供一个参数");
      return true;
    }
    uint32_t n;
    if (!epee::string_tools::get_xtype_from_string(n, local_args[0]))
    {
      fail_msg_writer() << tr("解析新地址数量失败：") << local_args[0];
      return true;
    }
    if (n > MAX_MNEW_ADDRESSES)
    {
      fail_msg_writer() << tr("新地址数量必须小于或等于 ") << MAX_MNEW_ADDRESSES;
      return true;
    }
    for (uint32_t i = 0; i < n; ++i)
    {
      m_wallet->add_subaddress(m_current_subaddress_account, tr("（未命名地址）"));
      print_address_sub(m_wallet->get_num_subaddresses(m_current_subaddress_account) - 1);
    }
  }
  else if (local_args[0] == "one-off")
  {
    CHECK_IF_BACKGROUND_SYNCING("cannot add address");
    local_args.erase(local_args.begin());
    std::string label;
    if (local_args.size() != 2)
    {
      fail_msg_writer() << tr("索引必须正好提供两个参数");
      return true;
    }
    uint32_t major, minor;
    if (!epee::string_tools::get_xtype_from_string(major, local_args[0]) || !epee::string_tools::get_xtype_from_string(minor, local_args[1]))
    {
      fail_msg_writer() << tr("解析索引失败：") << local_args[0] << " " << local_args[1];
      return true;
    }
    m_wallet->create_one_off_subaddress({major, minor});
    success_msg_writer() << boost::format(tr("地址 %u %u：%s")) % major % minor % m_wallet->get_subaddress_as_str({major, minor});
  }
  else if (local_args.size() >= 2 && local_args[0] == "label")
  {
    CHECK_IF_BACKGROUND_SYNCING("cannot modify address");
    if (!epee::string_tools::get_xtype_from_string(index, local_args[1]))
    {
      fail_msg_writer() << tr("解析索引失败：") << local_args[1];
      return true;
    }
    if (index >= m_wallet->get_num_subaddresses(m_current_subaddress_account))
    {
      fail_msg_writer() << tr("specify an index between 0 and ") << (m_wallet->get_num_subaddresses(m_current_subaddress_account) - 1);
      return true;
    }
    local_args.erase(local_args.begin());
    local_args.erase(local_args.begin());
    std::string label = boost::join(local_args, " ");
    m_wallet->set_subaddress_label({m_current_subaddress_account, index}, label);
    print_address_sub(index);
  }
  else if (local_args.size() <= 2 && epee::string_tools::get_xtype_from_string(index, local_args[0]))
  {
    local_args.erase(local_args.begin());
    uint32_t index_min = index;
    uint32_t index_max = index_min;
    if (local_args.size() > 0)
    {
      if (!epee::string_tools::get_xtype_from_string(index_max, local_args[0]))
      {
        fail_msg_writer() << tr("解析索引失败：") << local_args[0];
        return true;
      }
      local_args.erase(local_args.begin());
    }
    if (index_max < index_min)
      std::swap(index_min, index_max);
    if (index_min >= m_wallet->get_num_subaddresses(m_current_subaddress_account))
    {
      fail_msg_writer() << tr("<index_min> 已超出范围");
      return true;
    }
    if (index_max >= m_wallet->get_num_subaddresses(m_current_subaddress_account))
    {
      message_writer() << tr("<index_max> 超出范围");
      index_max = m_wallet->get_num_subaddresses(m_current_subaddress_account) - 1;
    }
    for (index = index_min; index <= index_max; ++index)
      print_address_sub(index);
  }
  else if (local_args[0] == "device")
  {
    index = 0;
    local_args.erase(local_args.begin());
    if (local_args.size() > 0)
    {
      if (!epee::string_tools::get_xtype_from_string(index, local_args[0]))
      {
        fail_msg_writer() << tr("解析索引失败：") << local_args[0];
        return true;
      }
      if (index >= m_wallet->get_num_subaddresses(m_current_subaddress_account))
      {
        fail_msg_writer() << tr("<index> 超出范围");
        return true;
      }
    }

    print_address_sub(index);
    m_wallet->device_show_address(m_current_subaddress_account, index, boost::none);
  }
  else
  {
    PRINT_USAGE(USAGE_ADDRESS);
  }

  return true;
}
//----------------------------------------------------------------------------------------------------
bool simple_wallet::print_integrated_address(const std::vector<std::string> &args/* = std::vector<std::string>()*/)
{
  crypto::hash8 payment_id;
  bool display_on_device = false;
  std::vector<std::string> local_args = args;

  if (local_args.size() > 0 && local_args[0] == "device")
  {
    local_args.erase(local_args.begin());
    display_on_device = true;
  }

  auto device_show_integrated = [this, display_on_device](crypto::hash8 payment_id)
  {
    if (display_on_device)
    {
      m_wallet->device_show_address(m_current_subaddress_account, 0, payment_id);
    }
  };

  if (local_args.size() > 1)
  {
    PRINT_USAGE(USAGE_INTEGRATED_ADDRESS);
    return true;
  }
  if (local_args.size() == 0)
  {
    if (m_current_subaddress_account != 0)
    {
      fail_msg_writer() << tr("只有账户 0 可以创建集成地址");
      return true;
    }
    payment_id = crypto::rand<crypto::hash8>();
    success_msg_writer() << tr("随机付款 ID：") << payment_id;
    success_msg_writer() << tr("匹配的集成地址：") << m_wallet->get_account().get_public_integrated_address_str(payment_id, m_wallet->nettype());
    device_show_integrated(payment_id);
    return true;
  }
  if(tools::wallet2::parse_short_payment_id(local_args.back(), payment_id))
  {
    if (m_current_subaddress_account != 0)
    {
      fail_msg_writer() << tr("只有账户 0 可以创建集成地址");
      return true;
    }
    success_msg_writer() << m_wallet->get_account().get_public_integrated_address_str(payment_id, m_wallet->nettype());
    device_show_integrated(payment_id);
    return true;
  }
  else {
    address_parse_info info;
    if(get_account_address_from_str(info, m_wallet->nettype(), local_args.back()))
    {
      if (info.has_payment_id)
      {
        success_msg_writer() << boost::format(tr("标准地址：%s, payment ID: %s")) %
          get_account_address_as_str(m_wallet->nettype(), false, info.address) % epee::string_tools::pod_to_hex(info.payment_id);
        device_show_integrated(info.payment_id);
      }
      else
      {
        success_msg_writer() << (info.is_subaddress ? tr("子地址：") : tr("标准地址：")) << get_account_address_as_str(m_wallet->nettype(), info.is_subaddress, info.address);
      }
      return true;
    }
  }
  fail_msg_writer() << tr("解析付款 ID 或地址失败");
  return true;
}
//----------------------------------------------------------------------------------------------------
bool simple_wallet::address_book(const std::vector<std::string> &args/* = std::vector<std::string>()*/)
{
  CHECK_IF_BACKGROUND_SYNCING("cannot get address book");

  if (args.size() == 0)
  {
  }
  else if (args.size() == 1 || (args[0] != "add" && args[0] != "delete"))
  {
    PRINT_USAGE(USAGE_ADDRESS_BOOK);
    return true;
  }
  else if (args[0] == "add")
  {
    cryptonote::address_parse_info info;
    if(!cryptonote::get_account_address_from_str_or_url(info, m_wallet->nettype(), args[1], m_wallet->is_dns_enabled(), oa_prompter))
    {
      fail_msg_writer() << tr("解析地址失败");
      return true;
    }
    size_t description_start = 2;
    std::string description;
    for (size_t i = description_start; i < args.size(); ++i)
    {
      if (i > description_start)
        description += " ";
      description += args[i];
    }
    m_wallet->add_address_book_row(info.address, info.has_payment_id ? &info.payment_id : NULL, description, info.is_subaddress);
  }
  else
  {
    size_t row_id;
    if(!epee::string_tools::get_xtype_from_string(row_id, args[1]))
    {
      fail_msg_writer() << tr("解析索引失败");
      return true;
    }
    m_wallet->delete_address_book_row(row_id);
  }
  auto address_book = m_wallet->get_address_book();
  if (address_book.empty())
  {
    success_msg_writer() << tr("地址簿为空。");
  }
  else
  {
    for (size_t i = 0; i < address_book.size(); ++i) {
      auto& row = address_book[i];
      success_msg_writer() << tr("索引：") << i;
      std::string address;
      if (row.m_has_payment_id)
        address = cryptonote::get_account_integrated_address_as_str(m_wallet->nettype(), row.m_address, row.m_payment_id);
      else
        address = get_account_address_as_str(m_wallet->nettype(), row.m_is_subaddress, row.m_address);
      success_msg_writer() << tr("地址：") << address;
      success_msg_writer() << tr("说明：") << row.m_description << "\n";
    }
  }
  return true;
}
//----------------------------------------------------------------------------------------------------
bool simple_wallet::set_tx_note(const std::vector<std::string> &args)
{
  CHECK_IF_BACKGROUND_SYNCING("cannot set tx note");

  if (args.size() == 0)
  {
    PRINT_USAGE(USAGE_SET_TX_NOTE);
    return true;
  }

  cryptonote::blobdata txid_data;
  if(!epee::string_tools::parse_hexstr_to_binbuff(args.front(), txid_data) || txid_data.size() != sizeof(crypto::hash))
  {
    fail_msg_writer() << tr("解析交易 ID 失败");
    return true;
  }
  crypto::hash txid = *reinterpret_cast<const crypto::hash*>(txid_data.data());

  std::string note = "";
  for (size_t n = 1; n < args.size(); ++n)
  {
    if (n > 1)
      note += " ";
    note += args[n];
  }
  m_wallet->set_tx_note(txid, note);

  return true;
}
//----------------------------------------------------------------------------------------------------
bool simple_wallet::get_tx_note(const std::vector<std::string> &args)
{
  CHECK_IF_BACKGROUND_SYNCING("cannot get tx note");

  if (args.size() != 1)
  {
    PRINT_USAGE(USAGE_GET_TX_NOTE);
    return true;
  }

  cryptonote::blobdata txid_data;
  if(!epee::string_tools::parse_hexstr_to_binbuff(args.front(), txid_data) || txid_data.size() != sizeof(crypto::hash))
  {
    fail_msg_writer() << tr("解析交易 ID 失败");
    return true;
  }
  crypto::hash txid = *reinterpret_cast<const crypto::hash*>(txid_data.data());

  std::string note = m_wallet->get_tx_note(txid);
  if (note.empty())
    success_msg_writer() << "no note found";
  else
    success_msg_writer() << "note found: " << note;

  return true;
}
//----------------------------------------------------------------------------------------------------
bool simple_wallet::set_description(const std::vector<std::string> &args)
{
  CHECK_IF_BACKGROUND_SYNCING("cannot set description");

  // 0 arguments allowed, for setting the description to empty string

  std::string description = "";
  for (size_t n = 0; n < args.size(); ++n)
  {
    if (n > 0)
      description += " ";
    description += args[n];
  }
  m_wallet->set_description(description);

  return true;
}
//----------------------------------------------------------------------------------------------------
bool simple_wallet::get_description(const std::vector<std::string> &args)
{
  CHECK_IF_BACKGROUND_SYNCING("cannot get description");

  if (args.size() != 0)
  {
    PRINT_USAGE(USAGE_GET_DESCRIPTION);
    return true;
  }

  std::string description = m_wallet->get_description();
  if (description.empty())
    success_msg_writer() << tr("未找到说明");
  else
    success_msg_writer() << tr("已找到说明：") << description;

  return true;
}
//----------------------------------------------------------------------------------------------------
bool simple_wallet::status(const std::vector<std::string> &args)
{
  uint64_t local_height = m_wallet->get_blockchain_current_height();
  uint32_t version = 0;
  bool ssl = false;
  if (!m_wallet->check_connection(&version, &ssl))
  {
    success_msg_writer() << "Refreshed " << local_height << "/?, no daemon connected";
    return true;
  }

  std::string err;
  uint64_t bc_height = get_daemon_blockchain_height(err);
  if (err.empty())
  {
    bool synced = local_height == bc_height;
    success_msg_writer() << "Refreshed " << local_height << "/" << bc_height << ", " << (synced ? "synced" : "syncing")
        << ", daemon RPC v" << get_version_string(version) << ", " << (ssl ? "SSL" : "no SSL");
  }
  else
  {
    fail_msg_writer() << "Refreshed " << local_height << "/?, daemon connection error";
  }
  return true;
}
//----------------------------------------------------------------------------------------------------
bool simple_wallet::wallet_info(const std::vector<std::string> &args)
{
  const multisig::multisig_account_status ms_status{m_wallet->get_multisig_status()};

  std::string description = m_wallet->get_description();
  if (description.empty())
  {
    description = "<Not set>"; 
  }
  message_writer() << tr("文件名：") << m_wallet->get_wallet_file();
  message_writer() << tr("说明：") << description;
  message_writer() << tr("地址：") << m_wallet->get_account().get_public_address_str(m_wallet->nettype());
  std::string type;
  if (m_wallet->watch_only())
    type = tr("仅观察");
  else if (ms_status.multisig_is_active)
    type = (boost::format(tr("%u/%u multisig%s")) % ms_status.threshold % ms_status.total % (ms_status.is_ready ? "" : " (not yet finalized)")).str();
  else if (m_wallet->is_background_wallet())
    type = tr("后台钱包");
  else
    type = tr("普通");
  message_writer() << tr("类型：") << type;
  message_writer() << tr("网络类型：") << (
    m_wallet->nettype() == cryptonote::TESTNET ? tr("测试网") :
    m_wallet->nettype() == cryptonote::STAGENET ? tr("预发布网络") : tr("主网"));
  if (ms_status.multisig_is_active)
  {
    type = tr("多重签名");
  }
  else if (m_wallet->is_polyseed())
  {
    type = tr("Polyseed");
  }
  else
  {
    type = tr("传统");
  }
  message_writer() << tr("助记词类型：") << type;
  return true;
}
//----------------------------------------------------------------------------------------------------
bool simple_wallet::sign(const std::vector<std::string> &args)
{
  CHECK_IF_BACKGROUND_SYNCING("cannot sign");
  if (m_wallet->key_on_device())
  {
    fail_msg_writer() << tr("硬件钱包不支持此命令");
    return true;
  }
  if (args.size() != 1 && args.size() != 2 && args.size() != 3)
  {
    PRINT_USAGE(USAGE_SIGN);
    return true;
  }
  if (m_wallet->watch_only())
  {
    fail_msg_writer() << tr("仅观察钱包无法签名");
    return true;
  }
  if (m_wallet->get_multisig_status().multisig_is_active)
  {
    fail_msg_writer() << tr("此多重签名钱包无法签名");
    return true;
  }

  tools::wallet2::message_signature_type_t message_signature_type = tools::wallet2::sign_with_spend_key;
  subaddress_index index{0, 0};
  for (unsigned int idx = 0; idx + 1 < args.size(); ++idx)
  {
    unsigned int a, b;
    if (sscanf(args[idx].c_str(), "%u,%u", &a, &b) == 2)
    {
      index.major = a;
      index.minor = b;
    }
    else if (args[idx] == "--spend")
    {
      message_signature_type = tools::wallet2::sign_with_spend_key;
    }
    else if (args[idx] == "--view")
    {
      message_signature_type = tools::wallet2::sign_with_view_key;
    }
    else
    {
      fail_msg_writer() << tr("子地址索引格式无效，也不是签名类型：") << args[idx];
      return true;
    }
  }

  const std::string &filename = args.back();
  std::string data;
  bool r = m_wallet->load_from_file(filename, data);
  if (!r)
  {
    fail_msg_writer() << tr("读取文件失败 ") << filename;
    return true;
  }

  SCOPED_WALLET_UNLOCK();

  std::string signature = m_wallet->sign(data, message_signature_type, index);
  success_msg_writer() << signature;
  return true;
}
//----------------------------------------------------------------------------------------------------
bool simple_wallet::verify(const std::vector<std::string> &args)
{
  if (args.size() != 3)
  {
    PRINT_USAGE(USAGE_VERIFY);
    return true;
  }
  std::string filename = args[0];
  std::string address_string = args[1];
  std::string signature= args[2];

  std::string data;
  bool r = m_wallet->load_from_file(filename, data);
  if (!r)
  {
    fail_msg_writer() << tr("读取文件失败 ") << filename;
    return true;
  }

  cryptonote::address_parse_info info;
  if(!cryptonote::get_account_address_from_str_or_url(info, m_wallet->nettype(), address_string, m_wallet->is_dns_enabled(), oa_prompter))
  {
    fail_msg_writer() << tr("解析地址失败");
    return true;
  }

  tools::wallet2::message_signature_result_t result = m_wallet->verify(data, info.address, signature);
  if (!result.valid)
  {
    fail_msg_writer() << tr("签名无效 from ") << address_string;
  }
  else
  {
    success_msg_writer() << tr("签名有效 from ") << address_string << (result.old ? " (using old signature algorithm)" : "") << " with " << (result.type == tools::wallet2::sign_with_spend_key ? "spend key" : result.type == tools::wallet2::sign_with_view_key ? "view key" : "unknown key combination (suspicious)");
  }
  return true;
}
//----------------------------------------------------------------------------------------------------
bool simple_wallet::export_key_images(const std::vector<std::string> &args_)
{
  if (m_wallet->key_on_device())
  {
    fail_msg_writer() << tr("硬件钱包不支持此命令");
    return true;
  }
  CHECK_IF_BACKGROUND_SYNCING("cannot export key images");
  auto args = args_;

  if (m_wallet->watch_only())
  {
    fail_msg_writer() << tr("仅观察钱包无法导出密钥镜像");
    return true;
  }

  bool all = false;
  if (args.size() >= 2 && args[0] == "all")
  {
    all = true;
    args.erase(args.begin());
  }

  if (args.size() != 1)
  {
    PRINT_USAGE(USAGE_EXPORT_KEY_IMAGES);
    return true;
  }

  std::string filename = args[0];
  if (m_wallet->confirm_export_overwrite() && !check_file_overwrite(filename))
    return true;

  SCOPED_WALLET_UNLOCK();

  try
  {
    if (!m_wallet->export_key_images(filename, all))
    {
      fail_msg_writer() << tr("保存文件失败 ") << filename;
      return true;
    }
  }
  catch (const std::exception &e)
  {
    LOG_ERROR("Error exporting key images: " << e.what());
    fail_msg_writer() << "Error exporting key images: " << e.what();
    return true;
  }

  success_msg_writer() << tr("已签名的密钥镜像已导出到 ") << filename;
  return true;
}
//----------------------------------------------------------------------------------------------------
bool simple_wallet::import_key_images(const std::vector<std::string> &args)
{
  if (m_wallet->key_on_device())
  {
    fail_msg_writer() << tr("硬件钱包不支持此命令");
    return true;
  }
  CHECK_IF_BACKGROUND_SYNCING("cannot import key images");
  if (!m_wallet->is_trusted_daemon())
  {
    fail_msg_writer() << tr("此命令需要可信守护进程，请使用 --trusted-daemon 启用");
    return true;
  }

  if (args.size() != 1)
  {
    PRINT_USAGE(USAGE_IMPORT_KEY_IMAGES);
    return true;
  }
  std::string filename = args[0];

  LOCK_IDLE_SCOPE();
  try
  {
    uint64_t spent = 0, unspent = 0;
    uint64_t height = m_wallet->import_key_images(filename, spent, unspent);
    success_msg_writer() << "Signed key images imported to height " << height << ", "
        << print_money(spent) << " spent, " << print_money(unspent) << " unspent"; 
  }
  catch (const std::exception &e)
  {
    fail_msg_writer() << "导入密钥镜像失败: " << e.what();
    return true;
  }

  return true;
}
//----------------------------------------------------------------------------------------------------
bool simple_wallet::hw_key_images_sync(const std::vector<std::string> &args)
{
  if (!m_wallet->key_on_device())
  {
    fail_msg_writer() << tr("此命令仅支持硬件钱包");
    return true;
  }
  if (!m_wallet->get_account().get_device().has_ki_cold_sync())
  {
    fail_msg_writer() << tr("硬件钱包不支持冷密钥镜像同步");
    return true;
  }

  LOCK_IDLE_SCOPE();
  key_images_sync_intern();
  return true;
}
//----------------------------------------------------------------------------------------------------
void simple_wallet::key_images_sync_intern(){
  try
  {
    message_writer(console_color_white, false) << tr("请在设备上确认密钥镜像同步");

    uint64_t spent = 0, unspent = 0;
    uint64_t height = m_wallet->cold_key_image_sync(spent, unspent);
    if (height > 0)
    {
      success_msg_writer() << tr("密钥镜像已同步到区块高度 ") << height;
      if (!m_wallet->is_trusted_daemon())
      {
        message_writer() << tr("当前使用不受信任的守护进程，无法确定哪些交易输出已花费。请使用受信任的守护进程并加上 --trusted-daemon，然后运行 rescan_spent");
      } else
      {
        success_msg_writer() << print_money(spent) << tr(" spent, ") << print_money(unspent) << tr(" unspent");
      }
    }
    else {
      fail_msg_writer() << tr("导入密钥镜像失败");
    }
  }
  catch (const std::exception &e)
  {
    fail_msg_writer() << tr("导入密钥镜像失败: ") << e.what();
  }
}
//----------------------------------------------------------------------------------------------------
bool simple_wallet::hw_reconnect(const std::vector<std::string> &args)
{
  if (!m_wallet->key_on_device())
  {
    fail_msg_writer() << tr("此命令仅支持硬件钱包");
    return true;
  }

  LOCK_IDLE_SCOPE();
  try
  {
    bool r = m_wallet->reconnect_device();
    if (!r){
      fail_msg_writer() << tr("重新连接设备失败");
    }
  }
  catch (const std::exception &e)
  {
    fail_msg_writer() << tr("重新连接设备失败: ") << tr(e.what());
    return true;
  }

  return true;
}
//----------------------------------------------------------------------------------------------------
bool simple_wallet::export_outputs(const std::vector<std::string> &args_)
{
  if (m_wallet->key_on_device())
  {
    fail_msg_writer() << tr("硬件钱包不支持此命令");
    return true;
  }
  CHECK_IF_BACKGROUND_SYNCING("cannot export outputs");
  auto args = args_;

  bool all = false;
  if (args.size() >= 2 && args[0] == "all")
  {
    all = true;
    args.erase(args.begin());
  }

  if (args.size() != 1)
  {
    PRINT_USAGE(USAGE_EXPORT_OUTPUTS);
    return true;
  }

  std::string filename = args[0];
  if (m_wallet->confirm_export_overwrite() && !check_file_overwrite(filename))
    return true;

  SCOPED_WALLET_UNLOCK();

  try
  {
    std::string data = m_wallet->export_outputs_to_str(all);
    bool r = m_wallet->save_to_file(filename, data);
    if (!r)
    {
      fail_msg_writer() << tr("保存文件失败 ") << filename;
      return true;
    }
  }
  catch (const std::exception &e)
  {
    LOG_ERROR("Error exporting outputs: " << e.what());
    fail_msg_writer() << "Error exporting outputs: " << e.what();
    return true;
  }

  success_msg_writer() << tr("输出已导出到 ") << filename;
  return true;
}
//----------------------------------------------------------------------------------------------------
bool simple_wallet::import_outputs(const std::vector<std::string> &args)
{
  if (m_wallet->key_on_device())
  {
    fail_msg_writer() << tr("硬件钱包不支持此命令");
    return true;
  }
  CHECK_IF_BACKGROUND_SYNCING("cannot import outputs");
  if (args.size() != 1)
  {
    PRINT_USAGE(USAGE_IMPORT_OUTPUTS);
    return true;
  }
  std::string filename = args[0];

  std::string data;
  bool r = m_wallet->load_from_file(filename, data);
  if (!r)
  {
    fail_msg_writer() << tr("读取文件失败 ") << filename;
    return true;
  }

  try
  {
    SCOPED_WALLET_UNLOCK();
    size_t n_outputs = m_wallet->import_outputs_from_str(data);
    success_msg_writer() << boost::lexical_cast<std::string>(n_outputs) << " outputs imported";
  }
  catch (const std::exception &e)
  {
    fail_msg_writer() << "Failed to import outputs " << filename << ": " << e.what();
    return true;
  }

  return true;
}
//----------------------------------------------------------------------------------------------------
bool simple_wallet::show_transfer(const std::vector<std::string> &args)
{
  if (args.size() != 1)
  {
    PRINT_USAGE(USAGE_SHOW_TRANSFER);
    return true;
  }

  cryptonote::blobdata txid_data;
  if(!epee::string_tools::parse_hexstr_to_binbuff(args.front(), txid_data) || txid_data.size() != sizeof(crypto::hash))
  {
    fail_msg_writer() << tr("解析交易 ID 失败");
    return true;
  }
  crypto::hash txid = *reinterpret_cast<const crypto::hash*>(txid_data.data());

  const uint64_t last_block_height = m_wallet->get_blockchain_current_height();

  std::list<std::pair<crypto::hash, tools::wallet2::payment_details>> payments;
  m_wallet->get_payments(payments, 0, (uint64_t)-1, m_current_subaddress_account);
  for (std::list<std::pair<crypto::hash, tools::wallet2::payment_details>>::const_iterator i = payments.begin(); i != payments.end(); ++i) {
    const tools::wallet2::payment_details &pd = i->second;
    if (pd.m_tx_hash == txid) {
      std::string payment_id = string_tools::pod_to_hex(i->first);
      if (payment_id.substr(16).find_first_not_of('0') == std::string::npos)
        payment_id = payment_id.substr(0,16);
      success_msg_writer() << "Incoming transaction found";
      success_msg_writer() << "txid: " << txid;
      success_msg_writer() << "Height: " << pd.m_block_height;
      success_msg_writer() << "Timestamp: " << tools::get_human_readable_timestamp(pd.m_timestamp);
      success_msg_writer() << "Amount: " << print_money(pd.m_amount);
      success_msg_writer() << "Payment ID: " << payment_id;
      if (pd.m_unlock_time < CRYPTONOTE_MAX_BLOCK_NUMBER)
      {
        uint64_t bh = std::max(pd.m_unlock_time, pd.m_block_height + CRYPTONOTE_DEFAULT_TX_SPENDABLE_AGE);
        const uint64_t confirmations = last_block_height > pd.m_block_height ? last_block_height - pd.m_block_height : 0;
        uint64_t last_block_reward = m_wallet->get_last_block_reward();
        uint64_t suggested_threshold = last_block_reward ? (pd.m_amount + last_block_reward - 1) / last_block_reward : 0;
        if (bh >= last_block_height)
          success_msg_writer() << "Locked: " << (bh - last_block_height) << " blocks to unlock";
        else if (confirmations < suggested_threshold)
          success_msg_writer() << std::to_string(confirmations) << " confirmations (" << suggested_threshold << " suggested for this amount)";
        else
          success_msg_writer() << std::to_string(confirmations) << " confirmations";
      }
      else
      {
        const uint64_t adjusted_time = m_wallet->get_daemon_adjusted_time();
        uint64_t threshold = adjusted_time + (m_wallet->use_fork_rules(2, 0) ? CRYPTONOTE_LOCKED_TX_ALLOWED_DELTA_SECONDS_V2 : CRYPTONOTE_LOCKED_TX_ALLOWED_DELTA_SECONDS_V1);
        if (threshold >= pd.m_unlock_time)
          success_msg_writer() << "unlocked for " << tools::get_human_readable_timespan(std::chrono::seconds(threshold - pd.m_unlock_time));
        else
          success_msg_writer() << "locked for " << tools::get_human_readable_timespan(std::chrono::seconds(pd.m_unlock_time - threshold));
      }
      success_msg_writer() << "Address index: " << pd.m_subaddr_index.minor;
      success_msg_writer() << "Note: " << m_wallet->get_tx_note(txid);
      return true;
    }
  }

  std::list<std::pair<crypto::hash, tools::wallet2::confirmed_transfer_details>> payments_out;
  m_wallet->get_payments_out(payments_out, 0, (uint64_t)-1, m_current_subaddress_account);
  for (std::list<std::pair<crypto::hash, tools::wallet2::confirmed_transfer_details>>::const_iterator i = payments_out.begin(); i != payments_out.end(); ++i) {
    if (i->first == txid)
    {
      const tools::wallet2::confirmed_transfer_details &pd = i->second;
      uint64_t change = pd.m_change == (uint64_t)-1 ? 0 : pd.m_change; // change may not be known
      uint64_t fee = pd.m_amount_in - pd.m_amount_out;
      std::string dests;
      for (const auto &d: pd.m_dests) {
        if (!dests.empty())
          dests += ", ";
        dests +=  d.address(m_wallet->nettype(), pd.m_payment_id) + ": " + print_money(d.amount);
      }
      std::string payment_id = string_tools::pod_to_hex(i->second.m_payment_id);
      if (payment_id.substr(16).find_first_not_of('0') == std::string::npos)
        payment_id = payment_id.substr(0,16);
      success_msg_writer() << "Outgoing transaction found";
      success_msg_writer() << "txid: " << txid;
      success_msg_writer() << "Height: " << pd.m_block_height;
      success_msg_writer() << "Timestamp: " << tools::get_human_readable_timestamp(pd.m_timestamp);
      success_msg_writer() << "Amount: " << print_money(pd.m_amount_in - change - fee);
      success_msg_writer() << "Payment ID: " << payment_id;
      success_msg_writer() << "Change: " << print_money(change);
      success_msg_writer() << "Fee: " << print_money(fee);
      success_msg_writer() << "Destinations: " << dests;
      success_msg_writer() << "Note: " << m_wallet->get_tx_note(txid);
      return true;
    }
  }

  try
  {
    std::vector<std::tuple<cryptonote::transaction, crypto::hash, bool>> process_txs;
    m_wallet->update_pool_state(process_txs);
    if (!process_txs.empty())
      m_wallet->process_pool_state(process_txs);

    std::list<std::pair<crypto::hash, tools::wallet2::pool_payment_details>> pool_payments;
    m_wallet->get_unconfirmed_payments(pool_payments, m_current_subaddress_account);
    for (std::list<std::pair<crypto::hash, tools::wallet2::pool_payment_details>>::const_iterator i = pool_payments.begin(); i != pool_payments.end(); ++i) {
      const tools::wallet2::payment_details &pd = i->second.m_pd;
      if (pd.m_tx_hash == txid)
      {
        std::string payment_id = string_tools::pod_to_hex(i->first);
        if (payment_id.substr(16).find_first_not_of('0') == std::string::npos)
          payment_id = payment_id.substr(0,16);
        success_msg_writer() << "Unconfirmed incoming transaction found in the txpool";
        success_msg_writer() << "txid: " << txid;
        success_msg_writer() << "Timestamp: " << tools::get_human_readable_timestamp(pd.m_timestamp);
        success_msg_writer() << "Amount: " << print_money(pd.m_amount);
        success_msg_writer() << "Payment ID: " << payment_id;
        success_msg_writer() << "Address index: " << pd.m_subaddr_index.minor;
        success_msg_writer() << "Note: " << m_wallet->get_tx_note(txid);
        if (i->second.m_double_spend_seen)
          success_msg_writer() << tr("网络检测到双花：此交易可能会被打包，也可能不会");
        return true;
      }
    }
  }
  catch (...)
  {
    fail_msg_writer() << "Failed to get pool state";
  }

  std::list<std::pair<crypto::hash, tools::wallet2::unconfirmed_transfer_details>> upayments;
  m_wallet->get_unconfirmed_payments_out(upayments, m_current_subaddress_account);
  for (std::list<std::pair<crypto::hash, tools::wallet2::unconfirmed_transfer_details>>::const_iterator i = upayments.begin(); i != upayments.end(); ++i) {
    if (i->first == txid)
    {
      const tools::wallet2::unconfirmed_transfer_details &pd = i->second;
      uint64_t amount = pd.m_amount_in;
      uint64_t fee = amount - pd.m_amount_out;
      std::string payment_id = string_tools::pod_to_hex(i->second.m_payment_id);
      if (payment_id.substr(16).find_first_not_of('0') == std::string::npos)
        payment_id = payment_id.substr(0,16);
      bool is_failed = pd.m_state == tools::wallet2::unconfirmed_transfer_details::failed;

      success_msg_writer() << (is_failed ? "Failed" : "Pending") << " outgoing transaction found";
      success_msg_writer() << "txid: " << txid;
      success_msg_writer() << "Timestamp: " << tools::get_human_readable_timestamp(pd.m_timestamp);
      success_msg_writer() << "Amount: " << print_money(amount - pd.m_change - fee);
      success_msg_writer() << "Payment ID: " << payment_id;
      success_msg_writer() << "Change: " << print_money(pd.m_change);
      success_msg_writer() << "Fee: " << print_money(fee);
      success_msg_writer() << "Note: " << m_wallet->get_tx_note(txid);
      return true;
    }
  }

  fail_msg_writer() << tr("未找到交易 ID");
  return true;
}
//----------------------------------------------------------------------------------------------------
bool simple_wallet::process_command(const std::vector<std::string> &args)
{
  return m_cmd_binder.process_command_vec(args);
}
//----------------------------------------------------------------------------------------------------
void simple_wallet::interrupt()
{
  if (m_in_manual_refresh.load(std::memory_order_relaxed))
  {
    m_wallet->stop();
  }
  else
  {
    stop();
  }
}
//----------------------------------------------------------------------------------------------------
void simple_wallet::commit_or_save(std::vector<tools::wallet2::pending_tx>& ptx_vector, bool do_not_relay)
{
  size_t i = 0;
  while (!ptx_vector.empty())
  {
    auto & ptx = ptx_vector.back();
    const crypto::hash txid = get_transaction_hash(ptx.tx);
    if (do_not_relay)
    {
      cryptonote::blobdata blob;
      tx_to_blob(ptx.tx, blob);
      const std::string blob_hex = epee::string_tools::buff_to_hex_nodelimer(blob);
      const std::string filename = "raw_monero_tx" + (ptx_vector.size() == 1 ? "" : ("_" + std::to_string(i++)));
      if (m_wallet->save_to_file(filename, blob_hex, true))
        success_msg_writer(true) << tr("交易已成功保存到 ") << filename << tr(", txid ") << txid;
      else
        fail_msg_writer() << tr("保存交易失败：") << filename << tr(", txid ") << txid;
    }
    else
    {
      m_wallet->commit_tx(ptx);
      success_msg_writer(true) << tr("交易已成功提交，交易 ID：") << txid << ENDL
      << tr("可以使用 `show_transfers` 命令查看其状态。");
    }
    // if no exception, remove element from vector
    ptx_vector.pop_back();
  }
}
//----------------------------------------------------------------------------------------------------
int main(int argc, char* argv[])
{
  TRY_ENTRY();

#ifdef WIN32
  // Activate UTF-8 support for Boost filesystem classes on Windows
  std::locale::global(boost::locale::generator().generate(""));
  boost::filesystem::path::imbue(std::locale());
#endif
  setlocale(LC_CTYPE, "");

  po::options_description desc_params(wallet_args::tr("钱包选项"));
  tools::wallet2::init_options(desc_params);
  command_line::add_arg(desc_params, arg_wallet_file);
  command_line::add_arg(desc_params, arg_wallet_dir);
  command_line::add_arg(desc_params, arg_generate_new_wallet);
  command_line::add_arg(desc_params, arg_generate_from_device);
  command_line::add_arg(desc_params, arg_generate_from_view_key);
  command_line::add_arg(desc_params, arg_generate_from_spend_key);
  command_line::add_arg(desc_params, arg_generate_from_keys);
  command_line::add_arg(desc_params, arg_generate_from_multisig_keys);
  command_line::add_arg(desc_params, arg_generate_from_json);
  command_line::add_arg(desc_params, arg_mnemonic_language);
  command_line::add_arg(desc_params, arg_command);

  command_line::add_arg(desc_params, arg_restore_deterministic_wallet );
  command_line::add_arg(desc_params, arg_restore_from_seed );
  command_line::add_arg(desc_params, arg_restore_multisig_wallet );
  command_line::add_arg(desc_params, arg_non_deterministic );
  command_line::add_arg(desc_params, arg_electrum_seed );
  command_line::add_arg(desc_params, arg_restore_height);
  command_line::add_arg(desc_params, arg_restore_date);
  command_line::add_arg(desc_params, arg_use_legacy_seed);
  command_line::add_arg(desc_params, arg_do_not_relay);
  command_line::add_arg(desc_params, arg_create_address_file);
  command_line::add_arg(desc_params, arg_subaddress_lookahead);
  command_line::add_arg(desc_params, arg_use_english_language_names);

  po::positional_options_description positional_options;
  positional_options.add(arg_command.name, -1);

  boost::optional<po::variables_map> vm;
  bool should_terminate = false;
  std::tie(vm, should_terminate) = wallet_args::main(
   argc, argv,
   "monero-wallet-cli [--wallet-file=<filename>|--generate-new-wallet=<filename>] [<COMMAND>]",
    sw::tr("这是 Monero 命令行钱包。它需要连接到 Monero 守护进程才能正常工作。\n警告：除非其他分叉内置了防止密钥复用的保护机制，否则不要在其他分叉上重复使用您的 Monero 密钥。这样做会损害您的隐私。"),
    desc_params,
    positional_options,
    [](const std::string &s, bool emphasis){ tools::scoped_message_writer(emphasis ? epee::console_color_white : epee::console_color_default, true) << s; },
    "monero-wallet-cli.log"
  );

  if (!vm)
  {
    return 1;
  }

  if (should_terminate)
  {
    return 0;
  }

  cryptonote::simple_wallet w;
  const bool r = w.init(*vm);
  CHECK_AND_ASSERT_MES(r, 1, sw::tr("初始化钱包失败"));

  std::vector<std::string> command = command_line::get_arg(*vm, arg_command);
  if (!command.empty())
  {
    if (!w.process_command(command))
      fail_msg_writer() << sw::tr("未知命令：") << command.front();
    w.stop();
    w.deinit();
  }
  else
  {
    tools::signal_handler::install([&w](int type) {
      if (tools::password_container::is_prompting.load())
      {
        // must be prompting for password so return and let the signal stop prompt
        return;
      }
#ifdef WIN32
      if (type == CTRL_C_EVENT)
#else
      if (type == SIGINT)
#endif
      {
        // if we're pressing ^C when refreshing, just stop refreshing
        w.interrupt();
      }
      else
      {
        w.stop();
      }
    });
    w.run();

    w.deinit();
  }
  return 0;
  CATCH_ENTRY_L0("main", 1);
}

// MMS ---------------------------------------------------------------------------------------------------

// Access to the message store, or more exactly to the list of the messages that can be changed
// by the idle thread, is guarded by the same mutex-based mechanism as access to the wallet
// as a whole and thus e.g. uses the "LOCK_IDLE_SCOPE" macro. This is a little over-cautious, but
// simple and safe. Care has to be taken however where MMS methods call other simplewallet methods
// that use "LOCK_IDLE_SCOPE" as this cannot be nested!

// Methods for commands like "export_multisig_info" usually read data from file(s) or write data
// to files. The MMS calls now those methods as well, to produce data for messages and to process data
// from messages. As it would be quite inconvenient for the MMS to write data for such methods to files
// first or get data out of result files after the call, those methods detect a call from the MMS and
// expect data as arguments instead of files and give back data by calling 'process_wallet_created_data'.

bool simple_wallet::user_confirms(const std::string &question)
{
   std::string answer = input_line(question, true);
   return !std::cin.eof() && command_line::is_yes(answer);
}

bool simple_wallet::user_confirms_auto_config()
{
  message_writer(console_color_red, true) << tr("警告：使用 MMS 自动配置机制并非无需信任");
  message_writer() << tr("恶意的自动配置管理者可能会发送其自己的钱包信息，而不是其他签名者的信息");
  message_writer() << tr("If in doubt do not use auto-config or at least compare configs using the \"mms config_checksum\" command");
  return user_confirms("Accept the risks and continue?");
}

bool simple_wallet::get_number_from_arg(const std::string &arg, uint32_t &number, const uint32_t lower_bound, const uint32_t upper_bound)
{
  bool valid = false;
  try
  {
    number = boost::lexical_cast<uint32_t>(arg);
    valid = (number >= lower_bound) && (number <= upper_bound);
  }
  catch(const boost::bad_lexical_cast &)
  {
  }
  return valid;
}

bool simple_wallet::choose_mms_processing(const std::vector<mms::processing_data> &data_list, uint32_t &choice)
{
  size_t choices = data_list.size();
  if (choices == 1)
  {
    choice = 0;
    return true;
  }
  mms::message_store& ms = m_wallet->get_message_store();
  message_writer() << tr("选择处理方式：");
  std::string text;
  for (size_t i = 0; i < choices; ++i)
  {
    const mms::processing_data &data = data_list[i];
    text = std::to_string(i+1) + ": ";
    switch (data.processing)
    {
    case mms::message_processing::sign_tx:
      text += tr("Sign tx");
      break;
    case mms::message_processing::send_tx:
    {
      mms::message m;
      ms.get_message_by_id(data.message_ids[0], m);
      if (m.type == mms::message_type::fully_signed_tx)
      {
        text += tr("Send the tx for submission to ");
      }
      else
      {
        text += tr("Send the tx for signing to ");
      }
      mms::authorized_signer signer = ms.get_signer(data.receiving_signer_index);
      text += ms.signer_to_string(signer, 50);
      break;
    }
    case mms::message_processing::submit_tx:
      text += tr("Submit tx");
      break;
    default:
      text += tr("未知");
      break;
    }
    message_writer() << text;
  }

  std::string line = input_line(tr("选择："));
  if (std::cin.eof() || line.empty())
  {
    return false;
  }
  bool choice_ok = get_number_from_arg(line, choice, 1, choices);
  if (choice_ok)
  {
    choice--;
  }
  else
  {
    fail_msg_writer() << tr("选择无效");
  }
  return choice_ok;
}

void simple_wallet::list_mms_messages(const std::vector<mms::message> &messages)
{
  message_writer() << boost::format("%4s %-4s %-30s %-21s %7s %3s %-15s %-40s") % tr("Id") % tr("I/O") % tr("授权签名者")
          % tr("消息类型") % tr("Height") % tr("R") % tr("消息状态") % tr("自");
  mms::message_store& ms = m_wallet->get_message_store();
  uint64_t now = (uint64_t)time(NULL);
  for (size_t i = 0; i < messages.size(); ++i)
  {
    const mms::message &m = messages[i];
    const mms::authorized_signer &signer = ms.get_signer(m.signer_index);
    bool highlight = (m.state == mms::message_state::ready_to_send) || (m.state == mms::message_state::waiting);
    message_writer(m.direction == mms::message_direction::out ? console_color_green : console_color_magenta, highlight) <<
            boost::format("%4s %-4s %-30s %-21s %7s %3s %-15s %-40s") %
            m.id %
            ms.message_direction_to_string(m.direction) %
            ms.signer_to_string(signer, 30) %
            ms.message_type_to_string(m.type) %
            m.wallet_height %
            m.round %
            ms.message_state_to_string(m.state) %
            (tools::get_human_readable_timestamp(m.modified) + ", " + tools::get_human_readable_timespan(std::chrono::seconds(now - m.modified)) + tr("前"));
  }
}

void simple_wallet::list_signers(const std::vector<mms::authorized_signer> &signers)
{
  message_writer() << boost::format("%2s %-20s %-s") % tr("#") % tr("标签") % tr("传输地址");
  message_writer() << boost::format("%2s %-20s %-s") % "" % tr("自动配置令牌") % tr("Monero 地址");
  for (size_t i = 0; i < signers.size(); ++i)
  {
    const mms::authorized_signer &signer = signers[i];
    std::string label = signer.label.empty() ? tr("<未设置>") : signer.label;
    std::string monero_address;
    if (signer.monero_address_known)
    {
      monero_address = get_account_address_as_str(m_wallet->nettype(), false, signer.monero_address);
    }
    else
    {
      monero_address = tr("<未设置>");
    }
    std::string transport_address = signer.transport_address.empty() ? tr("<未设置>") : signer.transport_address;
    message_writer() << boost::format("%2s %-20s %-s") % (i + 1) % label % transport_address;
    message_writer() << boost::format("%2s %-20s %-s") % "" % signer.auto_config_token % monero_address;
    message_writer() << "";
  }
}

void simple_wallet::add_signer_config_messages()
{
  mms::message_store& ms = m_wallet->get_message_store();
  std::string signer_config;
  ms.get_signer_config(signer_config);

  const std::vector<mms::authorized_signer> signers = ms.get_all_signers();
  mms::multisig_wallet_state state = get_multisig_wallet_state();
  uint32_t num_authorized_signers = ms.get_num_authorized_signers();
  for (uint32_t i = 1 /* without me */; i < num_authorized_signers; ++i)
  {
    ms.add_message(state, i, mms::message_type::signer_config, mms::message_direction::out, signer_config);
  }
}

void simple_wallet::show_message(const mms::message &m)
{
  mms::message_store& ms = m_wallet->get_message_store();
  const mms::authorized_signer &signer = ms.get_signer(m.signer_index);
  bool display_content;
  std::string sanitized_text;
  switch (m.type)
  {
  case mms::message_type::key_set:
  case mms::message_type::additional_key_set:
  case mms::message_type::note:
    display_content = true;
    sanitized_text = mms::message_store::get_sanitized_text(m.content, 1000);
    break;
  default:
    display_content = false;
  }
  uint64_t now = (uint64_t)time(NULL);
  message_writer() << "";
  message_writer() << tr("消息 ") << m.id;
  message_writer() << tr("收/发：") << ms.message_direction_to_string(m.direction);
  message_writer() << tr("类型：") << ms.message_type_to_string(m.type);
  message_writer() << tr("状态：") << boost::format(tr("%s since %s, %s ago")) %
          ms.message_state_to_string(m.state) % tools::get_human_readable_timestamp(m.modified) % tools::get_human_readable_timespan(std::chrono::seconds(now - m.modified));
  if (m.sent == 0)
  {
    message_writer() << tr("发送：从未");
  }
  else
  {
    message_writer() << boost::format(tr("Sent: %s, %s ago")) %
            tools::get_human_readable_timestamp(m.sent) % tools::get_human_readable_timespan(std::chrono::seconds(now - m.sent));
  }
  message_writer() << tr("授权签名者：") << ms.signer_to_string(signer, 100);
  message_writer() << tr("内容大小：") << m.content.length() << tr(" 字节");
  message_writer() << tr("内容：") << (display_content ? sanitized_text : tr("（二进制数据）"));

  if (m.type == mms::message_type::note)
  {
    // Showing a note and read its text is "processing" it: Set the state accordingly
    // which will also delete it from Bitmessage as a side effect
    // (Without this little "twist" it would never change the state, and never get deleted)
    ms.set_message_processed_or_sent(m.id);
  }
}

void simple_wallet::ask_send_all_ready_messages()
{
  mms::message_store& ms = m_wallet->get_message_store();
  std::vector<mms::message> ready_messages;
  const std::vector<mms::message> &messages = ms.get_all_messages();
  for (size_t i = 0; i < messages.size(); ++i)
  {
    const mms::message &m = messages[i];
    if (m.state == mms::message_state::ready_to_send)
    {
      ready_messages.push_back(m);
    }
  }
  if (ready_messages.size() != 0)
  {
    list_mms_messages(ready_messages);
    bool send = ms.get_auto_send();
    if (!send)
    {
      send = user_confirms(tr("现在发送这些消息吗？"));
    }
    if (send)
    {
      mms::multisig_wallet_state state = get_multisig_wallet_state();
      for (size_t i = 0; i < ready_messages.size(); ++i)
      {
        ms.send_message(state, ready_messages[i].id);
        ms.set_message_processed_or_sent(ready_messages[i].id);
      }
      success_msg_writer() << tr("已加入发送队列。");
    }
  }
}

bool simple_wallet::get_message_from_arg(const std::string &arg, mms::message &m)
{
  mms::message_store& ms = m_wallet->get_message_store();
  bool valid_id = false;
  uint32_t id;
  try
  {
    id = (uint32_t)boost::lexical_cast<uint32_t>(arg);
    valid_id = ms.get_message_by_id(id, m);
  }
  catch (const boost::bad_lexical_cast &)
  {
  }
  if (!valid_id)
  {
    fail_msg_writer() << tr("消息 ID 无效");
  }
  return valid_id;
}

void simple_wallet::mms_init(const std::vector<std::string> &args)
{
  if (args.size() != 3)
  {
    fail_msg_writer() << tr("usage: mms init <required_signers>/<authorized_signers> <own_label> <own_transport_address>");
    return;
  }
  mms::message_store& ms = m_wallet->get_message_store();
  if (ms.get_active())
  {
    if (!user_confirms(tr("MMS 已初始化。删除所有签名者信息和消息后重新初始化吗？")))
    {
      return;
    }
  }
  uint32_t num_required_signers;
  uint32_t num_authorized_signers;
  const std::string &mn = args[0];
  std::vector<std::string> numbers;
  boost::split(numbers, mn, boost::is_any_of("/"));
  bool mn_ok = (numbers.size() == 2)
               && get_number_from_arg(numbers[1], num_authorized_signers, 2, config::MULTISIG_MAX_SIGNERS)
               && get_number_from_arg(numbers[0], num_required_signers, 1, num_authorized_signers);
  if (!mn_ok)
  {
    fail_msg_writer() << tr("所需签名者数量和/或授权签名者数量错误");
    return;
  }
  LOCK_IDLE_SCOPE();
  ms.init(get_multisig_wallet_state(), args[1], args[2], num_authorized_signers, num_required_signers);
}

void simple_wallet::mms_info(const std::vector<std::string> &args)
{
  mms::message_store& ms = m_wallet->get_message_store();
  if (ms.get_active())
  {
    message_writer() << boost::format("The MMS is active for %s/%s multisig.")
            % ms.get_num_required_signers() % ms.get_num_authorized_signers();
  }
  else
  {
    message_writer() << tr("MMS 未启用。");
  }
}

void simple_wallet::mms_signer(const std::vector<std::string> &args)
{
  mms::message_store& ms = m_wallet->get_message_store();
  const std::vector<mms::authorized_signer> &signers = ms.get_all_signers();
  if (args.size() == 0)
  {
    // Without further parameters list all defined signers
    list_signers(signers);
    return;
  }

  uint32_t index;
  bool index_valid = get_number_from_arg(args[0], index, 1, ms.get_num_authorized_signers());
  if (index_valid)
  {
    index--;
  }
  else
  {
    fail_msg_writer() << tr("签名者编号无效：") + args[0];
    return;
  }
  if ((args.size() < 2) || (args.size() > 4))
  {
    fail_msg_writer() << tr("mms signer [<number> <label> [<transport_address> [<monero_address>]]]");
    return;
  }

  boost::optional<string> label = args[1];
  boost::optional<string> transport_address;
  if (args.size() >= 3)
  {
    transport_address = args[2];
  }
  boost::optional<cryptonote::account_public_address> monero_address;
  LOCK_IDLE_SCOPE();
  mms::multisig_wallet_state state = get_multisig_wallet_state();
  if (args.size() == 4)
  {
    cryptonote::address_parse_info info;
    bool ok = cryptonote::get_account_address_from_str_or_url(info, m_wallet->nettype(), args[3], m_wallet->is_dns_enabled(), oa_prompter);
    if (!ok)
    {
      fail_msg_writer() << tr("Monero 地址无效");
      return;
    }
    monero_address = info.address;
    const std::vector<mms::message> &messages = ms.get_all_messages();
    if ((messages.size() > 0) || state.multisig)
    {
      fail_msg_writer() << tr("当前钱包状态不允许再修改 Monero 地址");
      return;
    }
  }
  ms.set_signer(state, index, label, transport_address, monero_address);
}

void simple_wallet::mms_list(const std::vector<std::string> &args)
{
  mms::message_store& ms = m_wallet->get_message_store();
  if (args.size() != 0)
  {
    fail_msg_writer() << tr("Usage: mms list");
    return;
  }
  LOCK_IDLE_SCOPE();
  const std::vector<mms::message> &messages = ms.get_all_messages();
  list_mms_messages(messages);
}

void simple_wallet::mms_next(const std::vector<std::string> &args)
{
  mms::message_store& ms = m_wallet->get_message_store();
  if ((args.size() > 1) || ((args.size() == 1) && (args[0] != "sync")))
  {
    fail_msg_writer() << tr("Usage: mms next [sync]");
    return;
  }
  bool avail = false;
  std::vector<mms::processing_data> data_list;
  bool force_sync = false;
  uint32_t choice = 0;
  {
    LOCK_IDLE_SCOPE();
    if ((args.size() == 1) && (args[0] == "sync"))
    {
      // Force the MMS to process any waiting sync info although on its own it would just ignore
      // those messages because no need to process them can be seen
      force_sync = true;
    }
    string wait_reason;
    {
      avail = ms.get_processable_messages(get_multisig_wallet_state(), force_sync, data_list, wait_reason);
    }
    if (avail)
    {
      avail = choose_mms_processing(data_list, choice);
    }
    else if (!wait_reason.empty())
    {
      message_writer() << tr("没有下一步：") << wait_reason;
    }
  }
  if (avail)
  {
    mms::processing_data data = data_list[choice];
    bool command_successful = false;
    switch(data.processing)
    {
    case mms::message_processing::prepare_multisig:
      message_writer() << tr("prepare_multisig");
      command_successful = prepare_multisig_main(std::vector<std::string>(), true);
      break;

    case mms::message_processing::make_multisig:
    {
      message_writer() << tr("make_multisig");
      size_t number_of_key_sets = data.message_ids.size();
      std::vector<std::string> sig_args(number_of_key_sets + 1);
      sig_args[0] = std::to_string(ms.get_num_required_signers());
      for (size_t i = 0; i < number_of_key_sets; ++i)
      {
        mms::message m = ms.get_message_by_id(data.message_ids[i]);
        sig_args[i+1] = m.content;
      }
      command_successful = make_multisig_main(sig_args, true);
      break;
    }

    case mms::message_processing::exchange_multisig_keys:
    {
      message_writer() << tr("exchange_multisig_keys");
      size_t number_of_key_sets = data.message_ids.size();
      // Other than "make_multisig" only the key sets as parameters, no num_required_signers
      std::vector<std::string> sig_args(number_of_key_sets);
      for (size_t i = 0; i < number_of_key_sets; ++i)
      {
        mms::message m = ms.get_message_by_id(data.message_ids[i]);
        sig_args[i] = m.content;
      }
      // todo: update mms to enable 'key exchange force updating'
      command_successful = exchange_multisig_keys_main(sig_args, false, true);
      break;
    }

    case mms::message_processing::create_sync_data:
    {
      message_writer() << tr("export_multisig_info");
      std::vector<std::string> export_args;
      export_args.push_back("MMS");  // dummy filename
      command_successful = export_multisig_main(export_args, true);
      break;
    }

    case mms::message_processing::process_sync_data:
    {
      message_writer() << tr("import_multisig_info");
      std::vector<std::string> import_args;
      for (size_t i = 0; i < data.message_ids.size(); ++i)
      {
        mms::message m = ms.get_message_by_id(data.message_ids[i]);
        import_args.push_back(m.content);
      }
      command_successful = import_multisig_main(import_args, true);
      break;
    }

    case mms::message_processing::sign_tx:
    {
      message_writer() << tr("sign_multisig");
      std::vector<std::string> sign_args;
      mms::message m = ms.get_message_by_id(data.message_ids[0]);
      sign_args.push_back(m.content);
      command_successful = sign_multisig_main(sign_args, true);
      break;
    }

    case mms::message_processing::submit_tx:
    {
      message_writer() << tr("submit_multisig");
      std::vector<std::string> submit_args;
      mms::message m = ms.get_message_by_id(data.message_ids[0]);
      submit_args.push_back(m.content);
      command_successful = submit_multisig_main(submit_args, true);
      break;
    }

    case mms::message_processing::send_tx:
    {
      message_writer() << tr("发送交易");
      mms::message m = ms.get_message_by_id(data.message_ids[0]);
      LOCK_IDLE_SCOPE();
      ms.add_message(get_multisig_wallet_state(), data.receiving_signer_index, m.type, mms::message_direction::out,
                     m.content);
      command_successful = true;
      break;
    }

    case mms::message_processing::process_signer_config:
    {
      message_writer() << tr("处理签名者配置");
      LOCK_IDLE_SCOPE();
      mms::message m = ms.get_message_by_id(data.message_ids[0]);
      mms::authorized_signer me = ms.get_signer(0);
      mms::multisig_wallet_state state = get_multisig_wallet_state();
      if (!me.auto_config_running)
      {
        // If no auto-config is running, the config sent may be unsolicited or problematic
        // so show what arrived and ask for confirmation before taking it in
        std::vector<mms::authorized_signer> signers;
        ms.unpack_signer_config(state, m.content, signers);
        list_signers(signers);
        if (!user_confirms(tr("是否用上面显示的配置替换当前签名者配置？")))
        {
          break;
        }
        if (!user_confirms_auto_config())
        {
          message_writer() << tr("可以使用“mms delete”命令删除不需要的消息");
          break;
        }
      }
      ms.process_signer_config(state, m.content);
      ms.stop_auto_config();
      list_signers(ms.get_all_signers());
      command_successful = true;
      break;
    }

    case mms::message_processing::process_auto_config_data:
    {
      message_writer() << tr("处理自动配置数据");
      LOCK_IDLE_SCOPE();
      for (size_t i = 0; i < data.message_ids.size(); ++i)
      {
        ms.process_auto_config_data_message(data.message_ids[i]);
      }
      ms.stop_auto_config();
      list_signers(ms.get_all_signers());
      add_signer_config_messages();
      command_successful = true;
      break;
    }

    default:
      message_writer() << tr("没有准备好要处理的内容");
      break;
    }

    if (command_successful)
    {
      {
        LOCK_IDLE_SCOPE();
        ms.set_messages_processed(data);
        ask_send_all_ready_messages();
      }
    }
  }
}

void simple_wallet::mms_sync(const std::vector<std::string> &args)
{
  if (args.size() != 0)
  {
    fail_msg_writer() << tr("Usage: mms sync");
    return;
  }
  // Force the start of a new sync round, for exceptional cases where something went wrong
  // Can e.g. solve the problem "This signature was made with stale data" after trying to
  // create 2 transactions in a row somehow
  // Code is identical to the code for 'message_processing::create_sync_data'
  message_writer() << tr("export_multisig_info");
  std::vector<std::string> export_args;
  export_args.push_back("MMS");  // dummy filename
  export_multisig_main(export_args, true);
  ask_send_all_ready_messages();
}

void simple_wallet::mms_transfer(const std::vector<std::string> &args)
{
  // It's too complicated to check any arguments here, just let 'transfer_main' do the whole job
  transfer_main(args, true);
}

void simple_wallet::mms_delete(const std::vector<std::string> &args)
{
  if (args.size() != 1)
  {
    fail_msg_writer() << tr("Usage: mms delete (<message_id> | all)");
    return;
  }
  LOCK_IDLE_SCOPE();
  mms::message_store& ms = m_wallet->get_message_store();
  if (args[0] == "all")
  {
    if (user_confirms(tr("删除所有消息吗？")))
    {
      ms.delete_all_messages();
    }
  }
  else
  {
    mms::message m;
    bool valid_id = get_message_from_arg(args[0], m);
    if (valid_id)
    {
      // If only a single message and not all delete even if unsent / unprocessed
      ms.delete_message(m.id);
    }
  }
}

void simple_wallet::mms_send(const std::vector<std::string> &args)
{
  if (args.size() == 0)
  {
    ask_send_all_ready_messages();
    return;
  }
  else if (args.size() != 1)
  {
    fail_msg_writer() << tr("Usage: mms send [<message_id>]");
    return;
  }
  LOCK_IDLE_SCOPE();
  mms::message_store& ms = m_wallet->get_message_store();
  mms::message m;
  bool valid_id = get_message_from_arg(args[0], m);
  if (valid_id)
  {
    ms.send_message(get_multisig_wallet_state(), m.id);
  }
}

void simple_wallet::mms_receive(const std::vector<std::string> &args)
{
  if (args.size() != 0)
  {
    fail_msg_writer() << tr("Usage: mms receive");
    return;
  }
  std::vector<mms::message> new_messages;
  LOCK_IDLE_SCOPE();
  mms::message_store& ms = m_wallet->get_message_store();
  bool avail = ms.check_for_messages(get_multisig_wallet_state(), new_messages);
  if (avail)
  {
    list_mms_messages(new_messages);
  }
}

void simple_wallet::mms_export(const std::vector<std::string> &args)
{
  if (args.size() != 1)
  {
    fail_msg_writer() << tr("Usage: mms export <message_id>");
    return;
  }
  LOCK_IDLE_SCOPE();
  mms::message m;
  bool valid_id = get_message_from_arg(args[0], m);
  if (valid_id)
  {
    const std::string filename = "mms_message_content";
    if (m_wallet->save_to_file(filename, m.content))
    {
      success_msg_writer() << tr("消息内容已保存到：") << filename;
    }
    else
    {
      fail_msg_writer() << tr("保存消息内容失败");
    }
  }
}

void simple_wallet::mms_note(const std::vector<std::string> &args)
{
  mms::message_store& ms = m_wallet->get_message_store();
  if (args.size() == 0)
  {
    LOCK_IDLE_SCOPE();
    const std::vector<mms::message> &messages = ms.get_all_messages();
    for (size_t i = 0; i < messages.size(); ++i)
    {
      const mms::message &m = messages[i];
      if ((m.type == mms::message_type::note) && (m.state == mms::message_state::waiting))
      {
        show_message(m);
      }
    }
    return;
  }
  if (args.size() < 2)
  {
    fail_msg_writer() << tr("Usage: mms note [<label> <text>]");
    return;
  }
  uint32_t signer_index;
  bool found = ms.get_signer_index_by_label(args[0], signer_index);
  if (!found)
  {
    fail_msg_writer() << tr("未找到标签为此名称的签名者：") << args[0];
    return;
  }
  std::string note = "";
  for (size_t n = 1; n < args.size(); ++n)
  {
    if (n > 1)
    {
      note += " ";
    }
    note += args[n];
  }
  LOCK_IDLE_SCOPE();
  ms.add_message(get_multisig_wallet_state(), signer_index, mms::message_type::note,
                 mms::message_direction::out, note);
  ask_send_all_ready_messages();
}

void simple_wallet::mms_show(const std::vector<std::string> &args)
{
  if (args.size() != 1)
  {
    fail_msg_writer() << tr("Usage: mms show <message_id>");
    return;
  }
  LOCK_IDLE_SCOPE();
  mms::message m;
  bool valid_id = get_message_from_arg(args[0], m);
  if (valid_id)
  {
    show_message(m);
  }
}

void simple_wallet::mms_set(const std::vector<std::string> &args)
{
  bool set = args.size() == 2;
  bool query = args.size() == 1;
  if (!set && !query)
  {
    fail_msg_writer() << tr("Usage: mms set <option_name> [<option_value>]");
    return;
  }
  mms::message_store& ms = m_wallet->get_message_store();
  LOCK_IDLE_SCOPE();
  if (args[0] == "auto-send")
  {
    if (set)
    {
      bool result;
      bool ok = parse_bool(args[1], result);
      if (ok)
      {
        ms.set_auto_send(result);
      }
      else
      {
        fail_msg_writer() << tr("选项值错误");
      }
    }
    else
    {
      message_writer() << (ms.get_auto_send() ? tr("自动发送已开启") : tr("自动发送已关闭"));
    }
  }
  else
  {
    fail_msg_writer() << tr("未知选项");
  }
}

void simple_wallet::mms_help(const std::vector<std::string> &args)
{
  if (args.size() > 1)
  {
    fail_msg_writer() << tr("Usage: help mms [<subcommand>]");
    return;
  }
  std::vector<std::string> help_args;
  help_args.push_back("mms");
  if (args.size() == 1)
  {
    help_args.push_back(args[0]);
  }
  help(help_args);
}

void simple_wallet::mms_send_signer_config(const std::vector<std::string> &args)
{
  if (args.size() != 0)
  {
    fail_msg_writer() << tr("Usage: mms send_signer_config");
    return;
  }
  mms::message_store& ms = m_wallet->get_message_store();
  if (!ms.signer_config_complete())
  {
    fail_msg_writer() << tr("签名者配置尚未完成");
    return;
  }
  LOCK_IDLE_SCOPE();
  add_signer_config_messages();
  ask_send_all_ready_messages();
}

void simple_wallet::mms_start_auto_config(const std::vector<std::string> &args)
{
  mms::message_store& ms = m_wallet->get_message_store();
  uint32_t other_signers = ms.get_num_authorized_signers() - 1;
  size_t args_size = args.size();
  if ((args_size != 0) && (args_size != other_signers))
  {
    fail_msg_writer() << tr("Usage: mms start_auto_config [<label> <label> ...]");
    return;
  }
  if ((args_size == 0) && !ms.signer_labels_complete())
  {
    fail_msg_writer() << tr("仍有签名者未设置标签。请先完成标签设置，或在此处将标签作为参数提供。");
    return;
  }
  mms::authorized_signer me = ms.get_signer(0);
  if (me.auto_config_running)
  {
    if (!user_confirms(tr("自动配置已在运行。取消并重新开始吗？")))
    {
      return;
    }
  }
  LOCK_IDLE_SCOPE();
  mms::multisig_wallet_state state = get_multisig_wallet_state();
  if (args_size != 0)
  {
    // Set (or overwrite) all the labels except "me" from the arguments
    for (uint32_t i = 1; i < (other_signers + 1); ++i)
    {
      ms.set_signer(state, i, args[i - 1], boost::none, boost::none);
    }
  }
  ms.start_auto_config(state);
  // List the signers to show the generated auto-config tokens
  list_signers(ms.get_all_signers());
}

void simple_wallet::mms_config_checksum(const std::vector<std::string> &args)
{
  if (args.size() != 0)
  {
    fail_msg_writer() << tr("Usage: mms config_checksum");
    return;
  }
  mms::message_store& ms = m_wallet->get_message_store();
  LOCK_IDLE_SCOPE();
  message_writer() << ms.get_config_checksum();
}

void simple_wallet::mms_stop_auto_config(const std::vector<std::string> &args)
{
  if (args.size() != 0)
  {
    fail_msg_writer() << tr("Usage: mms stop_auto_config");
    return;
  }
  if (!user_confirms(tr("删除所有自动配置令牌并停止自动配置吗？")))
  {
    return;
  }
  mms::message_store& ms = m_wallet->get_message_store();
  LOCK_IDLE_SCOPE();
  ms.stop_auto_config();
}

void simple_wallet::mms_auto_config(const std::vector<std::string> &args)
{
  if (args.size() != 1)
  {
    fail_msg_writer() << tr("Usage: mms auto_config <auto_config_token>");
    return;
  }
  mms::message_store& ms = m_wallet->get_message_store();
  std::string adjusted_token;
  if (!ms.check_auto_config_token(args[0], adjusted_token))
  {
    fail_msg_writer() << tr("自动配置令牌无效");
    return;
  }
  if (!user_confirms_auto_config())
  {
    return;
  }
  mms::authorized_signer me = ms.get_signer(0);
  if (me.auto_config_running)
  {
    if (!user_confirms(tr("自动配置已在运行。取消并重新开始吗？")))
    {
      return;
    }
  }
  LOCK_IDLE_SCOPE();
  ms.add_auto_config_data_message(get_multisig_wallet_state(), adjusted_token);
  ask_send_all_ready_messages();
}

bool simple_wallet::mms(const std::vector<std::string> &args)
{
  CHECK_MULTISIG_ENABLED();
  try
  {
    m_wallet->get_multisig_wallet_state();
  }
  catch(const std::exception &e)
  {
    fail_msg_writer() << tr("此钱包不支持 MMS");
    return true;
  }

  try
  {
    mms::message_store& ms = m_wallet->get_message_store();
    if (args.size() == 0)
    {
      mms_info(args);
      return true;
    }

    const std::string &sub_command = args[0];
    std::vector<std::string> mms_args = args;
    mms_args.erase(mms_args.begin());

    if (sub_command == "init")
    {
      mms_init(mms_args);
      return true;
    }
    if (!ms.get_active())
    {
      fail_msg_writer() << tr("MMS 未启用。 Activate using the \"mms init\" command");
      return true;
    }
    else if (sub_command == "info")
    {
      mms_info(mms_args);
    }
    else if (sub_command == "signer")
    {
      mms_signer(mms_args);
    }
    else if (sub_command == "list")
    {
      mms_list(mms_args);
    }
    else if (sub_command == "next")
    {
      mms_next(mms_args);
    }
    else if (sub_command == "sync")
    {
      mms_sync(mms_args);
    }
    else if (sub_command == "transfer")
    {
      mms_transfer(mms_args);
    }
    else if (sub_command == "delete")
    {
      mms_delete(mms_args);
    }
    else if (sub_command == "send")
    {
      mms_send(mms_args);
    }
    else if (sub_command == "receive")
    {
      mms_receive(mms_args);
    }
    else if (sub_command == "export")
    {
      mms_export(mms_args);
    }
    else if (sub_command == "note")
    {
      mms_note(mms_args);
    }
    else if (sub_command == "show")
    {
      mms_show(mms_args);
    }
    else if (sub_command == "set")
    {
      mms_set(mms_args);
    }
    else if (sub_command == "help")
    {
      mms_help(mms_args);
    }
    else if (sub_command == "send_signer_config")
    {
      mms_send_signer_config(mms_args);
    }
    else if (sub_command == "start_auto_config")
    {
      mms_start_auto_config(mms_args);
    }
    else if (sub_command == "config_checksum")
    {
      mms_config_checksum(mms_args);
    }
    else if (sub_command == "stop_auto_config")
    {
      mms_stop_auto_config(mms_args);
    }
    else if (sub_command == "auto_config")
    {
      mms_auto_config(mms_args);
    }
    else
    {
      fail_msg_writer() << tr("MMS 子命令无效");
    }
  }
  catch (const tools::error::no_connection_to_daemon &e)
  {
    fail_msg_writer() << tr("MMS 命令错误：") << e.what() << " " << e.request();
  }
  catch (const std::exception &e)
  {
    fail_msg_writer() << tr("MMS 命令错误：") << e.what();
    PRINT_USAGE(USAGE_MMS);
    return true;
  }
  return true;
}
// End MMS ------------------------------------------------------------------------------------------------
