#!/bin/bash
#
# This Source Code Form is subject to the terms of the Mozilla Public
# License, v. 2.0. If a copy of the MPL was not distributed with this
# file, You can obtain one at http://mozilla.org/MPL/2.0/.

set -e

cd $(dirname "$0")
cd "$(git rev-parse --show-toplevel)"

source "tools/utils.sh"

function on_finish() {
    # TODO See workarounds below.
    find src/ -name '*.rs' \
        | xargs -d '\n' -n1 sed -i 's,// WORKAROUND TARPAULIN ,,g'
}

assert_installed "cargo-tarpaulin"

output_format=Html

args=$(getopt -l "xml" -o "x" -- "$@")

eval set -- "$args"

while [ $# -ge 1 ]; do
    case "$1" in
        --)
            # No more options left.
            shift
            break
            ;;
        -x|--xml)
            output_format=Xml
            shift
            ;;
    esac

    shift
done

trap on_finish EXIT

# TODO This is a workaround for a tarpaulin bug: https://github.com/xd009642/tarpaulin/issues/136#issuecomment-471340525
find src/ -name '*.rs' \
    | xargs -d '\n' -n1 sed -i 's,\(#\[inline.*\]\),// WORKAROUND TARPAULIN \0,'

# TODO This may be fixed in the future.
find src/ -name '*.rs' \
    | xargs -d '\n' -n1 sed -i 's,static_assertions::assert_eq_size!,// WORKAROUND TARPAULIN \0,'

cargo tarpaulin --features serde --force-clean --ignore-tests --timeout 1200 --out $output_format

if [ "$output_format" == "Html" ]; then
    echo
    echo "You can find the test coverage results at file://$(pwd)/tarpaulin-report.html"
fi
