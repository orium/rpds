#!/bin/bash
#
# This Source Code Form is subject to the terms of the Mozilla Public
# License, v. 2.0. If a copy of the MPL was not distributed with this
# file, You can obtain one at http://mozilla.org/MPL/2.0/.

set -e

cd $(dirname "$0")
cd "$(git rev-parse --show-toplevel)"

sed -i '/^$/q' README.md

grep --no-filename '//!' src/lib.rs \
    | sed 's,^//!\( \|\),,' \
    | grep -v '\[!\[.* documentation\](.*)\](.*/struct\..*\.html)' >> README.md
