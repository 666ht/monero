#!/data/data/com.termux/files/usr/bin/bash
# -*- coding: utf-8 -*-
#
# Monero Wallet CLI - Termux 纯中文菜单封装
#
# 设计目标：
# 1. 原程序标准输出只进入变量，不直接显示。
# 2. 原程序标准错误始终 2>/dev/null。
# 3. 后台使用 --command 执行钱包命令。
# 4. 仅提取数字、地址、状态等数据，再用中文重新排版。
# 5. 支持数字或中文菜单。
#
# 与本脚本配套的程序：
#   ./monero-wallet-cli

set -u

PROGRAM="./monero-wallet-cli"
WALLET_FILE=""
PASSWORD_FILE=""
DAEMON_ARGS=()

cleanup() {
    if [ -n "${PASSWORD_FILE}" ] && [ -f "${PASSWORD_FILE}" ]; then
        rm -f "${PASSWORD_FILE}" 2>/dev/null
    fi
}
trap cleanup EXIT
trap 'exit 130' INT TERM

clear_screen() {
    clear 2>/dev/null || true
}

pause_screen() {
    echo
    read -r -p "按回车键继续..." _
}

show_error() {
    echo "【错误】$1"
}

show_ok() {
    echo "【完成】$1"
}

require_program() {
    if [ ! -f "${PROGRAM}" ]; then
        show_error "未找到 ./monero-wallet-cli"
        return 1
    fi

    if [ ! -x "${PROGRAM}" ]; then
        chmod +x "${PROGRAM}" 2>/dev/null || true
    fi

    if [ ! -x "${PROGRAM}" ]; then
        show_error "monero-wallet-cli 没有执行权限"
        return 1
    fi

    return 0
}

choose_wallet() {
    echo "=========================================="
    echo "             选择钱包"
    echo "=========================================="
    echo

    read -r -p "请输入钱包文件路径： " WALLET_FILE

    if [ -z "${WALLET_FILE}" ]; then
        show_error "钱包文件不能为空"
        return 1
    fi

    if [ ! -f "${WALLET_FILE}" ]; then
        show_error "钱包文件不存在"
        return 1
    fi

    PASSWORD_FILE="$(mktemp "${TMPDIR:-/data/data/com.termux/files/usr/tmp}/monero-wallet-pass.XXXXXX" 2>/dev/null)"
    if [ -z "${PASSWORD_FILE}" ] || [ ! -f "${PASSWORD_FILE}" ]; then
        show_error "无法创建临时密码文件"
        return 1
    fi

    chmod 600 "${PASSWORD_FILE}" 2>/dev/null || true

    echo
    read -r -s -p "请输入钱包密码： " wallet_password
    echo
    printf '%s\n' "${wallet_password}" > "${PASSWORD_FILE}"
    unset wallet_password

    echo
    show_ok "钱包已设置"
    return 0
}

run_cli() {
    # 所有 stderr 明确丢弃。
    # stdout 被调用方捕获，因此原程序英文不会直接显示。
    "${PROGRAM}" \
        --wallet-file "${WALLET_FILE}" \
        --password-file "${PASSWORD_FILE}" \
        "${DAEMON_ARGS[@]}" \
        --command "$1" \
        2>/dev/null
}

extract_last_number() {
    printf '%s\n' "$1" |
        grep -oE '[0-9]+([.][0-9]+)?' |
        tail -n 1
}

query_balance() {
    clear_screen
    echo "=========================================="
    echo "                钱包余额"
    echo "=========================================="
    echo

    raw="$(run_cli "balance" 2>/dev/null)"
    rc=$?

    if [ "${rc}" -ne 0 ] || [ -z "${raw//[[:space:]]/}" ]; then
        show_error "读取余额失败，请检查钱包密码或守护进程连接"
        return
    fi

    total="$(printf '%s\n' "${raw}" |
        sed -nE 's/.*[Bb]alance:[[:space:]]*([0-9]+([.][0-9]+)?).*/\1/p' |
        head -n 1)"

    unlocked="$(printf '%s\n' "${raw}" |
        sed -nE 's/.*[Uu]nlocked[[:space:]]+[Bb]alance:[[:space:]]*([0-9]+([.][0-9]+)?).*/\1/p' |
        head -n 1)"

    # 某些版本使用同一行输出两个余额，补充数字提取。
    if [ -z "${total}" ]; then
        total="$(printf '%s\n' "${raw}" |
            grep -Eio 'balance:[[:space:]]*[0-9]+([.][0-9]+)?' |
            head -n 1 |
            grep -oE '[0-9]+([.][0-9]+)?$')"
    fi

    if [ -z "${unlocked}" ]; then
        unlocked="$(printf '%s\n' "${raw}" |
            grep -Eio 'unlocked[[:space:]]+balance:[[:space:]]*[0-9]+([.][0-9]+)?' |
            head -n 1 |
            grep -oE '[0-9]+([.][0-9]+)?$')"
    fi

    if [ -z "${total}" ] && [ -z "${unlocked}" ]; then
        show_error "没有提取到余额数据"
        return
    fi

    [ -n "${total}" ] && echo "总余额：${total} XMR"
    [ -n "${unlocked}" ] && echo "可用余额：${unlocked} XMR"

    echo
    echo "=========================================="
}

query_address() {
    clear_screen
    echo "=========================================="
    echo "                钱包地址"
    echo "=========================================="
    echo

    raw="$(run_cli "address" 2>/dev/null)"
    rc=$?

    if [ "${rc}" -ne 0 ] || [ -z "${raw//[[:space:]]/}" ]; then
        show_error "读取钱包地址失败"
        return
    fi

    address="$(printf '%s\n' "${raw}" |
        grep -oE '[48][0-9A-Za-z]{90,110}' |
        head -n 1)"

    if [ -z "${address}" ]; then
        show_error "没有提取到有效钱包地址"
        return
    fi

    echo "钱包地址："
    echo
    echo "${address}"
    echo
    echo "=========================================="
}

query_status() {
    clear_screen
    echo "=========================================="
    echo "                同步状态"
    echo "=========================================="
    echo

    raw="$(run_cli "status" 2>/dev/null)"
    rc=$?

    if [ "${rc}" -ne 0 ] || [ -z "${raw//[[:space:]]/}" ]; then
        show_error "读取同步状态失败，请检查网络或守护进程"
        return
    fi

    # 常见格式：Height 1234567 / 1234567
    current="$(printf '%s\n' "${raw}" |
        grep -Eio 'height[[:space:]]*[=:]?[[:space:]]*[0-9]+' |
        grep -oE '[0-9]+' |
        head -n 1)"

    target="$(printf '%s\n' "${raw}" |
        grep -Eio '/[[:space:]]*[0-9]{4,}' |
        grep -oE '[0-9]+' |
        head -n 1)"

    # 备用格式：从结果中取连续大整数
    if [ -z "${current}" ]; then
        current="$(printf '%s\n' "${raw}" |
            grep -oE '[0-9]{5,}' |
            head -n 1)"
    fi

    if [ -z "${current}" ]; then
        show_error "没有提取到同步高度"
        return
    fi

    echo "当前同步高度：${current}"

    if [ -n "${target}" ]; then
        echo "区块链高度：${target}"
        remaining="$(awk -v a="${target}" -v b="${current}" 'BEGIN { r=a-b; if (r<0) r=0; printf "%.0f", r }')"
        echo "剩余区块：${remaining}"
        if [ "${remaining}" -eq 0 ]; then
            echo "同步状态：已完成"
        else
            echo "同步状态：正在同步"
        fi
    else
        echo "同步状态：已获取"
    fi

    echo
    echo "=========================================="
}

refresh_wallet() {
    clear_screen
    echo "=========================================="
    echo "                刷新钱包"
    echo "=========================================="
    echo
    echo "正在刷新，请稍候..."
    echo

    raw="$(run_cli "refresh" 2>/dev/null)"
    rc=$?

    if [ "${rc}" -ne 0 ]; then
        show_error "刷新失败，请检查网络连接和守护进程"
        return
    fi

    # 不显示原程序输出，只提取最后一个高度数字。
    height="$(printf '%s\n' "${raw}" |
        grep -oE '[0-9]{5,}' |
        tail -n 1)"

    if [ -n "${height}" ]; then
        show_ok "刷新完成"
        echo "当前高度：${height}"
    else
        show_ok "刷新完成"
    fi

    echo
    echo "=========================================="
}

query_transfers() {
    clear_screen
    echo "=========================================="
    echo "                交易记录"
    echo "=========================================="
    echo

    raw="$(run_cli "show_transfers all" 2>/dev/null)"
    rc=$?

    if [ "${rc}" -ne 0 ] || [ -z "${raw//[[:space:]]/}" ]; then
        show_error "读取交易记录失败"
        return
    fi

    # 仅重构可识别数据；不输出原始英文表格。
    ids="$(printf '%s\n' "${raw}" |
        grep -oE '[0-9a-fA-F]{64}' |
        head -n 10)"

    amounts="$(printf '%s\n' "${raw}" |
        grep -Eo '[0-9]+([.][0-9]+)?' |
        head -n 20)"

    count=0
    while IFS= read -r txid; do
        [ -z "${txid}" ] && continue
        count=$((count + 1))
        echo "第${count}笔交易："
        echo "交易编号：${txid}"
        echo
    done <<EOF_TXID
${ids}
EOF_TXID

    if [ "${count}" -eq 0 ]; then
        show_error "没有提取到交易记录"
        return
    fi

    echo "已读取交易数量：${count}"
    echo
    echo "=========================================="
}

set_daemon() {
    clear_screen
    echo "=========================================="
    echo "              设置守护进程"
    echo "=========================================="
    echo

    read -r -p "请输入节点地址（例如 127.0.0.1:18081）： " daemon
    if [ -z "${daemon}" ]; then
        show_error "节点地址不能为空"
        return
    fi

    DAEMON_ARGS=(--daemon-address "${daemon}")
    show_ok "节点已设置为：${daemon}"
}

main_menu() {
    while true; do
        clear_screen

        echo "=========================================="
        echo "           Monero 钱包中文控制台"
        echo "=========================================="
        echo
        echo "当前钱包：${WALLET_FILE}"
        if [ "${#DAEMON_ARGS[@]}" -ge 2 ]; then
            echo "当前节点：${DAEMON_ARGS[1]}"
        else
            echo "当前节点：默认节点"
        fi
        echo
        echo "------------------------------------------"
        echo "  1. 查询余额"
        echo "  2. 查询钱包地址"
        echo "  3. 查询同步状态"
        echo "  4. 刷新钱包"
        echo "  5. 查询交易记录"
        echo "  6. 设置守护进程"
        echo "  7. 重新选择钱包"
        echo "  8. 退出"
        echo "------------------------------------------"
        echo

        read -r -p "请输入编号或中文命令： " choice

        case "${choice}" in
            1|查询|余额|查询余额)
                query_balance
                pause_screen
                ;;
            2|地址|钱包地址|查询地址)
                query_address
                pause_screen
                ;;
            3|状态|同步|同步状态)
                query_status
                pause_screen
                ;;
            4|刷新|刷新钱包|同步钱包)
                refresh_wallet
                pause_screen
                ;;
            5|交易|交易记录|查询交易)
                query_transfers
                pause_screen
                ;;
            6|节点|守护进程|设置节点)
                set_daemon
                pause_screen
                ;;
            7|换钱包|重新选择|重新选择钱包)
                if [ -n "${PASSWORD_FILE}" ] && [ -f "${PASSWORD_FILE}" ]; then
                    rm -f "${PASSWORD_FILE}" 2>/dev/null
                fi
                PASSWORD_FILE=""
                WALLET_FILE=""
                if ! choose_wallet; then
                    pause_screen
                fi
                ;;
            8|退出|退出程序|q|Q|exit)
                clear_screen
                echo "程序已退出。"
                exit 0
                ;;
            *)
                show_error "无效选项，请输入 1～8 或中文命令"
                pause_screen
                ;;
        esac
    done
}

clear_screen

if ! require_program; then
    exit 1
fi

if ! choose_wallet; then
    exit 1
fi

echo
show_ok "中文菜单启动成功"
pause_screen

main_menu
