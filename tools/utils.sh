# This Source Code Form is subject to the terms of the Mozilla Public
# License, v. 2.0. If a copy of the MPL was not distributed with this
# file, You can obtain one at http://mozilla.org/MPL/2.0/.

function assert_installed {
    local bin="$1"

    if ! [ -x "$(which "$bin" 2> /dev/null)" ]; then
        echo "error: $bin not installed." >&2
        exit 1
    fi
}

function os {
    if test -n "$TRAVIS_OS_NAME"; then
        echo "$TRAVIS_OS_NAME"
    else
        echo linux
    fi
}

function unit_tests_build {
    # TODO Maybe in the future there will be a better way.  See https://github.com/rust-lang/cargo/issues/1924.
    cargo test --no-run --message-format=json 2>/dev/null \
        | jq -r "select(.profile.test == true) | .filenames[]" \
        | tac -s'/' | head -1
}

function project_name {
    cargo pkgid | tac -s'/' | head -1 | cut -d'#' -f1
}

function project_version {
    cargo pkgid | tac -s'/' | head -1 | cut -d'#' -f2
}
