#!/bin/bash
#
# This Source Code Form is subject to the terms of the Mozilla Public
# License, v. 2.0. If a copy of the MPL was not distributed with this
# file, You can obtain one at http://mozilla.org/MPL/2.0/.

set -e

cd $(dirname "$0")
cd "$(git rev-parse --show-toplevel)"

source "tools/utils.sh"

function set_version {
    local version=$1

    sed -i "0,/version = .*$/s//version = \"$version\"/" Cargo.toml

    # Update version in `Cargo.lock`.
    cargo update -p $(project_name) --offline
}

if [ $(git symbolic-ref --short HEAD) != master ]; then
    echo "Not in master branch." >&2
    exit 1
fi

if [ $(git status --porcelain | wc -l) -ne 0 ]; then
    echo "Working directory is not clean." >&2
    exit 1
fi

echo "Current version is $(project_version)."

echo -n "Which version do you want to release? "
read release_version

if ! grep "^## " release-notes.md | head -1 | grep --silent "^## $release_version$"; then
    echo "You forgot to update the release notes." >&2
    exit 1
fi

echo -n "Which will be the next version? "
read next_version

if ! echo "$next_version" | grep --silent -- "-pre$"; then
    echo 'Next version must end in `-pre`.' >&2
fi

echo
echo "Current version: $(project_version)"
echo "Release version: $release_version"
echo "Next version:    $next_version"
echo
echo -n 'Does this look right [yes/no]? '

read answer

if [ "$answer" != "yes" ]; then
    exit 0
fi

echo -n "Running tests... "

if ! ./tools/check.sh 2>/dev/null > /dev/null; then
    echo "It failed :(" >&2
    exit 0
fi

echo "done."

set_version "$release_version"

git commit -am "Release v${release_version}."
git tag --sign -a "v${release_version}" -m "$(project_name) version ${release_version}."

set_version "$next_version"

git commit -am "Bump to version $next_version."

echo "Check if everything is alright.  If so do:"
echo
echo "  git checkout \"v${release_version}\" && cargo publish && git checkout master && git push --follow-tags"
echo
