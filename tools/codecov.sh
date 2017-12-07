#!/bin/bash
#
# This Source Code Form is subject to the terms of the Mozilla Public
# License, v. 2.0. If a copy of the MPL was not distributed with this
# file, You can obtain one at http://mozilla.org/MPL/2.0/.

set -e

# TODO Maybe in the future there will be a better way.  See https://github.com/rust-lang/cargo/issues/1924.
build=$(cargo test --no-run --message-format=json 2>/dev/null | \
    jq -r "select(.profile.test == true) | .filenames[]" | \
    rev | cut -d'/' -f 1 | rev)

kcov --verify target/cov \
    --exclude-pattern='cargo/registry/,test' \
    --exclude-region='#[cfg(test)]' \
    --exclude-line='unreachable!' \
    target/debug/$build $@ 2>&1 >/dev/null

echo "You can find the test coverage results at file://$(pwd)/target/cov/$build/index.html"
