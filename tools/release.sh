#!/bin/bash

set -e

MAIN_BRANCH=main

cd $(dirname "$0")
cd "$(git rev-parse --show-toplevel)"

source "tools/utils.sh"

function set_version {
    local version=$1

    sed -i "0,/version = .*$/s//version = \"$version\"/" Cargo.toml

    # Update version in `Cargo.lock`.
    cargo update -w --offline
}

if [ $(git symbolic-ref --short HEAD) != $MAIN_BRANCH ]; then
    echo "Not in $MAIN_BRANCH branch." >&2
    exit 1
fi

if [ $(git status --porcelain --untracked-files=no | wc -l) -ne 0 ]; then
    echo "Working directory is not clean." >&2
    exit 1
fi

echo 'Checking if local branch is up to date...'

git remote update origin > /dev/null 2> /dev/null

if git status -uno | grep --silent "behind"; then
    echo "Local branch is not up to date." >&2
    exit 1
fi

echo "Current version is $(project_version)."

echo -n "Which version do you want to release? "
read release_version

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

while ! grep "^## " release-notes.md | head -1 | grep --silent "^## $release_version$"; do
    echo
    echo "There's no entry for this version in the release notes."
    echo -n "Go ahead and add them and press enter when you're done... "
    read
done

set_version "$release_version"

git commit -am "Release v${release_version}."
git tag --sign -a "v${release_version}" -m "$(project_name) version ${release_version}."

set_version "$next_version"

git commit -am "Bump to version $next_version."

echo "Check if everything is alright.  If so do:"
echo
echo "  git push --atomic origin $MAIN_BRANCH v${release_version} && git checkout v${release_version} && cargo publish && git checkout $MAIN_BRANCH"
echo
