function assert_installed() {
    local bin="$1"

    if ! [ -x "$(which "$bin" 2> /dev/null)" ]; then
        echo "error: $bin not installed." >&2
        exit 1
    fi
}
