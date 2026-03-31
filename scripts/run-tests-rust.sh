#!/bin/sh
# Run Rust workspace tests, then the same integration suite as ML `run-tests.sh`, with URWEB
# pointing at the Rust compiler binary (urweb-rust). Intended for `samu rust-test`.
set -e
srcdir="${1:-.}"
builddir="${2:-.}"
URWEB="${URWEB:-$(cd "$builddir" && pwd)/bin/urweb-rust}"

(
  cd "$srcdir" || exit 1
  cargo test --workspace --all-targets
)

URWEB="$URWEB" URWEB_ARGS="${URWEB_ARGS:-}" sh "$srcdir/scripts/run-tests.sh" "$srcdir" "$builddir"
