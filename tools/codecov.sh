#!/bin/bash
#
# This Source Code Form is subject to the terms of the Mozilla Public
# License, v. 2.0. If a copy of the MPL was not distributed with this
# file, You can obtain one at http://mozilla.org/MPL/2.0/.

set -e

cd $(dirname "$0")
cd "$(git rev-parse --show-toplevel)"

source "tools/utils.sh"

assert_installed "jq"
assert_installed "kcov"

# If we don't pass this to rustc, functions that are unreachable from the unit
# tests will be removed from the binary and would not count as uncovered code.
export RUSTFLAGS='-C link-dead-code'

build=$(unit_tests_build)

kcov --verify target/cov \
    --exclude-pattern='cargo/registry/,test' \
    --exclude-line='unreachable!' \
    target/debug/$build $@ 2>&1 >/dev/null

# TODO The symbolic link that kcov generates is broken, so we have to do this workaround.
report_dir=$(readlink target/cov/$build | sed 's,/*$,,' | rev | cut -d/ -f1 | rev)

echo "You can find the test coverage results at file://$(pwd)/target/cov/$report_dir/index.html"
