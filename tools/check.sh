#!/bin/bash
#
# This Source Code Form is subject to the terms of the Mozilla Public
# License, v. 2.0. If a copy of the MPL was not distributed with this
# file, You can obtain one at http://mozilla.org/MPL/2.0/.

set -e

cd $(dirname "$0")
cd "$(git rev-parse --show-toplevel)"

source "tools/utils.sh"

RED='\033[0;31m'
GREEN='\033[0;32m'
NC='\033[0m'

function on_failure {
    echo >&2
    echo -e "${RED}Whoopsie-daisy: something failed!$NC" >&2
}

assert_installed "cargo"

trap on_failure ERR

function check_basic {
    echo 'Building:'
    cargo build --features fatal-warnings --all-targets
    echo 'Testing:'
    cargo test  --features fatal-warnings --all-targets
    # Weirdly, the `cargo test ... --all-targets ...` above does not run the tests in the documentation, so we run the
    # doc tests like this.
    # See https://github.com/rust-lang/cargo/issues/6669.
    echo 'Testing doc:'
    cargo test  --features fatal-warnings --doc
    echo 'Checking the benchmarks:'
    cargo bench --features fatal-warnings -- --test
    echo 'Checking documentation:'
    cargo doc   --features fatal-warnings --no-deps
}

function check_doc_url_links {
    assert_installed "cargo-deadlinks"

    echo 'Checking doc url links:'
    cargo deadlinks
}

function check_unused_deps {
    assert_installed "cargo-machete"

    echo 'Checking unused dependencies:'
    cargo machete
}

function check_packaging {
    echo 'Checking packaging:'
    cargo package --allow-dirty
}

function check_fmt {
    assert_installed "cargo-fmt"

    echo 'Checking code format:'
    cargo fmt -- --check
}

function check_toml_fmt {
    assert_installed "taplo"

    echo 'Checking toml format:'
    taplo fmt --check
}

function check_readme {
    assert_installed "cargo-rdme"

    echo 'Checking readme:'
	cargo rdme --check
}

function check_msrv {
    assert_installed "cargo-msrv"

    echo 'Checking the minimum supported rust version:'
    cargo msrv verify
}

function check_clippy {
    assert_installed "cargo-clippy"

    echo 'Checking with clippy:'
    cargo clippy --all-targets -- -D warnings
}

to_run=(basic doc_url_links unused_deps packaging fmt toml_fmt readme msrv clippy)

if [ $# -ge 1 ]; then
    to_run=("$@")
fi

for check in "${to_run[@]}"; do
    check_$check
done

echo
echo -e "${GREEN}Everything looks lovely!$NC"

exit 0
