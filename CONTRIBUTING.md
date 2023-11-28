# Contributing to rpds

Thank you for your interest in contributing to rpds. We appreciate it!

It is a good idea for you to open an issue before you start working on non-trivial features. This way we can discuss if
the feature is desirable and how to best design and implement it.

## Useful tools

If you are contributing with a pull request you probably want to know about these scripts:

* [`./tools/check.sh`](tools/check.sh) — Checks that everything is fine. This includes checking that everything
  builds, the unit tests pass, and the code is correctly formatted. If you need to format the code run
  `cargo fmt`.
* [`./tools/codecov.sh`](tools/codecov.sh) — Creates a code coverage report. There is not a strict code coverage
  threshold, but we do want pretty much everything tested.
* [`cargo rdme`](https://crates.io/crates/cargo-rdme) — Updates the README with the crate’s rustdoc.
