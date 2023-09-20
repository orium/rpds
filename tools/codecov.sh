#!/bin/bash
#
# This Source Code Form is subject to the terms of the Mozilla Public
# License, v. 2.0. If a copy of the MPL was not distributed with this
# file, You can obtain one at http://mozilla.org/MPL/2.0/.

set -e

cd $(dirname "$0")
cd "$(git rev-parse --show-toplevel)"

source "tools/utils.sh"

assert_installed "cargo-tarpaulin"

output_format=html

args=$(getopt -o '' -l xml -- "$@")

eval set -- "$args"

while [ $# -ge 1 ]; do
    case "$1" in
        --)
            # No more options left.
            shift
            break
            ;;
        --xml)
            output_format=xml
            ;;
    esac

    shift
done

# TODO it seems the `--force-clean` is not working.
cargo clean
cargo tarpaulin --force-clean --ignore-panics --engine llvm --timeout 1200 --out $output_format

if [ "$output_format" == "html" ]; then
    echo
    echo "You can find the test coverage results at file://$(pwd)/tarpaulin-report.html"
fi
