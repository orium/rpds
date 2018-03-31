#!/bin/bash
#
# This Source Code Form is subject to the terms of the Mozilla Public
# License, v. 2.0. If a copy of the MPL was not distributed with this
# file, You can obtain one at http://mozilla.org/MPL/2.0/.

set -e

cd $(dirname "$0")
cd "$(git rev-parse --show-toplevel)"

cargo build --features fatal-warnings,serde
cargo test  --features fatal-warnings,serde
QUICK_BENCH=true cargo bench --features fatal-warnings,serde
cargo doc   --features fatal-warnings,serde
cargo deadlinks
cargo package
cargo +nightly fmt -- --write-mode=diff
./tools/update-readme.sh --check

exit 0
