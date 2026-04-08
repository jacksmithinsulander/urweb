#!/bin/sh
# Run only the executable-level integration suite with URWEB pointing at the Rust compiler binary
# (urweb-rust). Intended for `samu rust-test`.
set -e
srcdir="${1:-.}"
builddir="${2:-.}"
URWEB="${URWEB:-$(cd "$builddir" && pwd)/bin/urweb-rust}"

URWEB="$URWEB" URWEB_ARGS="${URWEB_ARGS:-}" sh "$srcdir/scripts/run-tests.sh" "$srcdir" "$builddir"
