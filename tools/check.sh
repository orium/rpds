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
    echo
    echo -e "${RED}Whoopsie-daisy: something failed!$NC"
}

# `cargo-deadlinks` does not work on windows.
test "$TRAVIS_OS_NAME" = windows || assert_installed "cargo-deadlinks"
assert_installed "cargo-fmt"

trap on_failure ERR

cargo build --features fatal-warnings,serde --all-targets
cargo test  --features fatal-warnings,serde
cargo bench --features fatal-warnings,serde -- --test
cargo doc   --features fatal-warnings,serde

# `cargo-deadlinks` does not work on windows.
test "$TRAVIS_OS_NAME" = windows || cargo deadlinks

cargo package --allow-dirty
cargo fmt -- --check
./tools/update-readme.sh --check

echo
echo -e "${GREEN}Everything looks lovely!$NC"

exit 0
