#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Termux wrapper for monero-wallet-cli.

- Keeps the original monero-wallet-cli binary untouched.
- Uses a real PTY, so readline/password/input interaction still works.
- Translates common English console prompts/messages to Simplified Chinese.
- Unknown text is passed through unchanged.
"""

import os
import pty
import re
import sys

SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
BINARY = os.path.join(SCRIPT_DIR, "monero-wallet-cli")

# Longest/specific phrases first. These are output-only replacements; command
# names, addresses, hashes, amounts and other wallet data are not modified.
TRANSLATIONS = [
    ("Specify wallet file name", "请指定钱包文件名"),
    ("Wallet file name", "钱包文件名"),
    ("Please enter wallet password", "请输入钱包密码"),
    ("Enter wallet password", "请输入钱包密码"),
    ("Enter new wallet password", "请输入新的钱包密码"),
    ("Please confirm password", "请确认密码"),
    ("Confirm password", "确认密码"),
    ("Password confirmation", "密码确认"),
    ("Password", "密码"),
    ("Wallet password", "钱包密码"),
    ("New password", "新密码"),
    ("Wallet name", "钱包名称"),
    ("Generate new wallet", "生成新钱包"),
    ("Restore wallet", "恢复钱包"),
    ("Restore from seed", "从助记词恢复"),
    ("Enter seed", "请输入助记词"),
    ("Mnemonic", "助记词"),
    ("Seed", "助记词"),
    ("Restore height", "恢复高度"),
    ("Restore date", "恢复日期"),
    ("Starting wallet refresh", "开始刷新钱包"),
    ("Starting refresh", "开始刷新"),
    ("Refresh done", "刷新完成"),
    ("Refresh finished", "刷新完成"),
    ("Refresh failed", "刷新失败"),
    ("Blocks received", "收到区块"),
    ("blocks received", "收到区块"),
    ("Current block", "当前区块"),
    ("Current height", "当前高度"),
    ("Blockchain height", "区块链高度"),
    ("Block height", "区块高度"),
    ("Remaining", "剩余"),
    ("remaining", "剩余"),
    ("Syncing", "正在同步"),
    ("Synchronizing", "正在同步"),
    ("Synchronization", "同步"),
    ("Sync complete", "同步完成"),
    ("Syncing wallet", "正在同步钱包"),
    ("Scanning", "正在扫描"),
    ("Scan complete", "扫描完成"),
    ("Rescanning", "正在重新扫描"),
    ("Rescan complete", "重新扫描完成"),
    ("Balance", "余额"),
    ("Unlocked balance", "可用余额"),
    ("unlocked balance", "可用余额"),
    ("Currently selected account", "当前选中的账户"),
    ("Selected account", "选中账户"),
    ("Account", "账户"),
    ("Subaddress", "子地址"),
    ("Address", "地址"),
    ("Integrated address", "集成地址"),
    ("Payment ID", "支付 ID"),
    ("Transaction", "交易"),
    ("Transactions", "交易"),
    ("Transaction ID", "交易 ID"),
    ("Transaction hash", "交易哈希"),
    ("Transaction key", "交易密钥"),
    ("Destination address", "目标地址"),
    ("Destination", "目标"),
    ("Amount", "金额"),
    ("Fee", "手续费"),
    ("Priority", "优先级"),
    ("Payment", "付款"),
    ("Incoming transfers", "收款记录"),
    ("Outgoing transfers", "转账记录"),
    ("Pending transactions", "待处理交易"),
    ("Failed transactions", "失败交易"),
    ("Confirmed", "已确认"),
    ("Unconfirmed", "未确认"),
    ("Locked", "已锁定"),
    ("Unlocked", "已解锁"),
    ("Transfer", "转账"),
    ("Transfer failed", "转账失败"),
    ("Transfer succeeded", "转账成功"),
    ("Transaction successfully sent", "交易已成功发送"),
    ("Transaction created successfully", "交易创建成功"),
    ("Transaction was relayed", "交易已广播"),
    ("Transaction was not relayed", "交易未广播"),
    ("Command not found", "未找到命令"),
    ("Unknown command", "未知命令"),
    ("Invalid command", "无效命令"),
    ("Invalid argument", "无效参数"),
    ("Invalid address", "无效地址"),
    ("Invalid amount", "无效金额"),
    ("Invalid password", "密码错误"),
    ("Bad password", "密码错误"),
    ("Wrong password", "密码错误"),
    ("Password mismatch", "两次密码不一致"),
    ("Failed to read password", "读取密码失败"),
    ("Failed to open wallet", "打开钱包失败"),
    ("Failed to save wallet", "保存钱包失败"),
    ("Wallet not found", "未找到钱包"),
    ("Wallet already exists", "钱包已存在"),
    ("Wallet is already open", "钱包已经打开"),
    ("Wallet is not open", "钱包尚未打开"),
    ("Wallet opened", "钱包已打开"),
    ("Wallet closed", "钱包已关闭"),
    ("Wallet saved", "钱包已保存"),
    ("Wallet successfully", "钱包操作成功"),
    ("Error:", "错误："),
    ("ERROR:", "错误："),
    ("Warning:", "警告："),
    ("WARNING:", "警告："),
    ("Info:", "信息："),
    ("NOTICE:", "提示："),
    ("Failed:", "失败："),
    ("Success:", "成功："),
    ("Unable to", "无法"),
    ("Could not", "无法"),
    ("Failed to", "无法"),
    ("not found", "未找到"),
    ("not available", "不可用"),
    ("not connected", "未连接"),
    ("connected", "已连接"),
    ("Connection refused", "连接被拒绝"),
    ("Connection timed out", "连接超时"),
    ("Disconnected from daemon", "已与守护进程断开连接"),
    ("Daemon", "守护进程"),
    ("daemon", "守护进程"),
    ("Starting daemon", "正在启动守护进程"),
    ("Daemon is busy", "守护进程正忙"),
    ("untrusted daemon", "不受信任的守护进程"),
    ("trusted daemon", "受信任的守护进程"),
    ("The following daemon is not trusted", "以下守护进程不受信任"),
    ("Mining", "挖矿"),
    ("Mining started", "挖矿已开始"),
    ("Mining stopped", "挖矿已停止"),
    ("Multisig", "多重签名"),
    ("multisig", "多重签名"),
    ("Freeze", "冻结"),
    ("Frozen", "已冻结"),
    ("Thaw", "解冻"),
    ("Unfreezing", "正在解冻"),
    ("Export", "导出"),
    ("Import", "导入"),
    ("Description", "描述"),
    ("Note", "备注"),
    ("Save", "保存"),
    ("Delete", "删除"),
    ("Yes", "是"),
    ("No", "否"),
    ("Success", "成功"),
    ("failed", "失败"),
    ("Enter", "请输入"),
    ("Please", "请"),
    ("Done", "完成"),
    ("Press Enter to continue", "按回车键继续"),
    ("Press enter to continue", "按回车键继续"),
]

# Replace longer phrases before shorter terms.
TRANSLATIONS.sort(key=lambda x: len(x[0]), reverse=True)
_translation_re = re.compile(
    "|".join(re.escape(src) for src, _ in TRANSLATIONS)
)
_translation_map = dict(TRANSLATIONS)

def translate(text: str) -> str:
    return _translation_re.sub(lambda m: _translation_map[m.group(0)], text)

class StreamTranslator:
    def __init__(self) -> None:
        self.pending = ""

    def feed(self, data: bytes) -> bytes:
        # Console output is UTF-8 on Termux. Keep decoding loss-tolerant so a
        # malformed byte from an external component never breaks the wallet.
        text = data.decode("utf-8", errors="replace")
        self.pending += text

        out = []
        while True:
            positions = [p for p in (self.pending.find("\n"),
                                     self.pending.find("\r")) if p >= 0]
            if not positions:
                break
            end = min(positions) + 1
            out.append(translate(self.pending[:end]))
            self.pending = self.pending[end:]

        # Interactive prompts often have no newline. Flush a prompt when it
        # clearly ends in ": " or "? ", while retaining long partial fragments.
        if self.pending.endswith((": ", "? "))):
            out.append(translate(self.pending))
            self.pending = ""
        elif len(self.pending) > 4096:
            out.append(translate(self.pending[:-512]))
            self.pending = self.pending[-512:]

        return "".join(out).encode("utf-8", errors="replace")

    def flush(self) -> bytes:
        if not self.pending:
            return b""
        out = translate(self.pending)
        self.pending = ""
        return out.encode("utf-8", errors="replace")

def main() -> int:
    if not os.path.isfile(BINARY):
        print("错误：未找到同目录下的 ./monero-wallet-cli", file=sys.stderr)
        print("请把本脚本和 monero-wallet-cli 放在同一个目录。", file=sys.stderr)
        return 1

    if not os.access(BINARY, os.X_OK):
        print("错误：./monero-wallet-cli 没有执行权限", file=sys.stderr)
        print("请运行：chmod +x ./monero-wallet-cli", file=sys.stderr)
        return 1

    translator = StreamTranslator()

    def master_read(fd: int) -> bytes:
        try:
            data = os.read(fd, 4096)
        except OSError:
            return b""
        if not data:
            return b""
        converted = translator.feed(data)
        if converted:
            os.write(sys.stdout.fileno(), converted)
        # Return empty because we already wrote translated output ourselves.
        return b""

    status = pty.spawn([BINARY, *sys.argv[1:]], master_read=master_read)

    tail = translator.flush()
    if tail:
        os.write(sys.stdout.fileno(), tail)

    if os.WIFEXITED(status):
        return os.WEXITSTATUS(status)
    if os.WIFSIGNALED(status):
        return 128 + os.WTERMSIG(status)
    return 1

if __name__ == "__main__":
    raise SystemExit(main())
