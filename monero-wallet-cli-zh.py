#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Termux wrapper for monero-wallet-cli.

The original ./monero-wallet-cli is left untouched. This wrapper:
  * starts it inside a real PTY;
  * keeps interactive input/password/readline behavior;
  * translates common English console text to Simplified Chinese;
  * passes unknown text and wallet data through unchanged.

Usage:
  chmod +x ./monero-wallet-cli ./monero-wallet-cli-zh.py
  ./monero-wallet-cli-zh.py [monero-wallet-cli arguments...]
"""

import os
import pty
import re
import selectors
import signal
import struct
import subprocess
import sys
import termios
import fcntl
import tty

SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
BINARY = os.path.join(SCRIPT_DIR, "monero-wallet-cli")

# Specific phrases first. These are output-only replacements; command names,
# addresses, hashes, amounts and other wallet data are not changed.
TRANSLATIONS = [
    ("Specify wallet file name", "请指定钱包文件名"),
    ("Wallet file name", "钱包文件名"),
    ("Please enter wallet password", "请输入钱包密码"),
    ("Enter wallet password", "请输入钱包密码"),
    ("Enter new wallet password", "请输入新的钱包密码"),
    ("Please confirm password", "请确认密码"),
    ("Confirm password", "确认密码"),
    ("Password confirmation", "密码确认"),
    ("Wallet password", "钱包密码"),
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
    ("Sync complete", "同步完成"),
    ("Syncing wallet", "正在同步钱包"),
    ("Syncing", "正在同步"),
    ("Synchronizing", "正在同步"),
    ("Synchronization", "同步"),
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
    ("Integrated address", "集成地址"),
    ("Payment ID", "支付 ID"),
    ("Transaction ID", "交易 ID"),
    ("Transaction hash", "交易哈希"),
    ("Transaction key", "交易密钥"),
    ("Destination address", "目标地址"),
    ("Incoming transfers", "收款记录"),
    ("Outgoing transfers", "转账记录"),
    ("Pending transactions", "待处理交易"),
    ("Failed transactions", "失败交易"),
    ("Confirmed", "已确认"),
    ("Unconfirmed", "未确认"),
    ("Locked", "已锁定"),
    ("Unlocked", "已解锁"),
    ("Transaction successfully sent", "交易已成功发送"),
    ("Transaction created successfully", "交易创建成功"),
    ("Transaction was relayed", "交易已广播"),
    ("Transaction was not relayed", "交易未广播"),
    ("Transfer failed", "转账失败"),
    ("Transfer succeeded", "转账成功"),
    ("Transaction", "交易"),
    ("Transactions", "交易"),
    ("Transfer", "转账"),
    ("Destination", "目标"),
    ("Amount", "金额"),
    ("Fee", "手续费"),
    ("Priority", "优先级"),
    ("Payment", "付款"),
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
    ("Connection refused", "连接被拒绝"),
    ("Connection timed out", "连接超时"),
    ("Disconnected from daemon", "已与守护进程断开连接"),
    ("The following daemon is not trusted", "以下守护进程不受信任"),
    ("Daemon is busy", "守护进程正忙"),
    ("untrusted daemon", "不受信任的守护进程"),
    ("trusted daemon", "受信任的守护进程"),
    ("Starting daemon", "正在启动守护进程"),
    ("Daemon", "守护进程"),
    ("daemon", "守护进程"),
    ("Mining started", "挖矿已开始"),
    ("Mining stopped", "挖矿已停止"),
    ("Mining", "挖矿"),
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
    ("Press Enter to continue", "按回车键继续"),
    ("Press enter to continue", "按回车键继续"),
    ("Success", "成功"),
    ("failed", "失败"),
]

TRANSLATIONS.sort(key=lambda x: len(x[0]), reverse=True)
_translation_re = re.compile("|".join(re.escape(src) for src, _ in TRANSLATIONS))
_translation_map = dict(TRANSLATIONS)

def translate(text: str) -> str:
    return _translation_re.sub(lambda m: _translation_map[m.group(0)], text)


class StreamTranslator:
    def __init__(self):
        self.pending = ""

    def feed(self, data: bytes) -> bytes:
        text = data.decode("utf-8", errors="replace")
        self.pending += text
        out = []

        # Flush complete console lines.
        while True:
            positions = [p for p in (self.pending.find("\n"), self.pending.find("\r")) if p >= 0]
            if not positions:
                break
            end = min(positions) + 1
            out.append(translate(self.pending[:end]))
            self.pending = self.pending[end:]

        # Interactive prompts often do not end with a newline.
        if self.pending.endswith((": ", "? ")):
            out.append(translate(self.pending))
            self.pending = ""
        elif len(self.pending) > 8192:
            out.append(translate(self.pending[:-1024]))
            self.pending = self.pending[-1024:]

        return "".join(out).encode("utf-8", errors="replace")

    def flush(self) -> bytes:
        if not self.pending:
            return b""
        out = translate(self.pending)
        self.pending = ""
        return out.encode("utf-8", errors="replace")


def copy_window_size(src_fd: int, dst_fd: int) -> None:
    try:
        size = fcntl.ioctl(src_fd, termios.TIOCGWINSZ, b"\0" * 8)
        fcntl.ioctl(dst_fd, termios.TIOCSWINSZ, size)
    except (OSError, AttributeError):
        pass


def main() -> int:
    if not os.path.isfile(BINARY):
        print("错误：未找到同目录下的 ./monero-wallet-cli", file=sys.stderr)
        print("请把本脚本和 monero-wallet-cli 放在同一个目录。", file=sys.stderr)
        return 1

    if not os.access(BINARY, os.X_OK):
        print("错误：./monero-wallet-cli 没有执行权限", file=sys.stderr)
        print("请运行：chmod +x ./monero-wallet-cli", file=sys.stderr)
        return 1

    master, slave = pty.openpty()
    copy_window_size(sys.stdin.fileno(), slave)

    child = subprocess.Popen(
        [BINARY, *sys.argv[1:]],
        stdin=slave,
        stdout=slave,
        stderr=slave,
        close_fds=True,
        start_new_session=True,
    )
    os.close(slave)

    def on_winch(_signum, _frame):
        copy_window_size(sys.stdin.fileno(), master)

    old_attrs = None
    translator = StreamTranslator()
    selector = selectors.DefaultSelector()
    master_open = True

    try:
        old_attrs = termios.tcgetattr(sys.stdin.fileno())
        tty.setraw(sys.stdin.fileno())

        signal.signal(signal.SIGWINCH, on_winch)
        selector.register(master, selectors.EVENT_READ, "pty")
        selector.register(sys.stdin.fileno(), selectors.EVENT_READ, "stdin")

        while master_open:
            for key, _ in selector.select(timeout=0.1):
                if key.data == "pty":
                    try:
                        data = os.read(master, 16384)
                    except OSError:
                        data = b""
                    if not data:
                        master_open = False
                        selector.unregister(master)
                        break
                    converted = translator.feed(data)
                    if converted:
                        os.write(sys.stdout.fileno(), converted)

                else:
                    try:
                        data = os.read(sys.stdin.fileno(), 4096)
                    except OSError:
                        data = b""
                    if data:
                        os.write(master, data)
                    else:
                        selector.unregister(sys.stdin.fileno())

            if child.poll() is not None and not master_open:
                break

        tail = translator.flush()
        if tail:
            os.write(sys.stdout.fileno(), tail)
    finally:
        selector.close()
        try:
            os.close(master)
        except OSError:
            pass
        if old_attrs is not None:
            termios.tcsetattr(sys.stdin.fileno(), termios.TCSADRAIN, old_attrs)

    return child.returncode if child.returncode is not None else 0


if __name__ == "__main__":
    raise SystemExit(main())
