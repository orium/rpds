#!/bin/bash
#
# This file is part of rpds.
#
# rpds is free software: you can redistribute it and/or modify
# it under the terms of the GNU Lesser General Public License as published
# by the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# rpds is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU Lesser General Public License for more details.
#
# You should have received a copy of the GNU Lesser General Public License
# along with rpds.  If not, see <http://www.gnu.org/licenses/>.

set -e

# TODO Maybe in the future there will be a better way.  See https://github.com/rust-lang/cargo/issues/1924.
build=$(cargo test --no-run --message-format=json 2>/dev/null | \
    jq -r "select(.profile.test == true) | .filenames[]" | \
    rev | cut -d'/' -f 1 | rev)

kcov --verify target/cov \
    --exclude-pattern=/.cargo,/usr/lib \
    --exclude-region='#[cfg(test)]' \
    --exclude-line='unreachable!' \
    target/debug/$build 2>&1 >/dev/null

mv "target/cov/$build/" "target/coverage/"

echo "You can find the test coverage results at file://$(pwd)/target/coverage/index.html"
