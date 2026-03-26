#!/bin/sh
# Minimal test using the Rust compiler (bin/urweb-rust).
# Same as run-tests-minimal.sh but uses urweb-rust.
set -e
srcdir="${1:-.}"
builddir="${2:-.}"

URWEB="$(cd "$builddir" && pwd)/bin/urweb-rust"
TESTDB="/tmp/urweb_rust_minimal.db"
TESTPID="/tmp/urweb_rust_minimal.pid"
export URWEB
. "$srcdir/tests/lib.sh"

free_port 8080
sleep 1

if [ ! -f "$URWEB" ]; then
  echo "FAIL: urweb-rust not found at $URWEB" >&2
  echo "Build it with: ninja urweb-rust (or samu urweb-rust)" >&2
  exit 1
fi

rm -f "$TESTDB" "$TESTPID"
echo "=== Minimal test (Rust): demo/hello ==="
"$URWEB" -boot -noEmacs -dbms sqlite -db "$TESTDB" "$srcdir/demo/hello" 2>/dev/null || { echo "FAIL: minimal-rust/compile"; exit 1; }
echo "PASS: minimal-rust/compile"
"$srcdir/demo/hello.exe" -q -a 127.0.0.1 & echo $! > "$TESTPID"
sleep 1
_hello=$(curl -s 'http://localhost:8080/Hello/main' | sed -e '$s/[[:space:]]*$//')
_exp=$(cat "$srcdir/tests/hello.html" | sed -e '$s/[[:space:]]*$//')
_expf=$(mktemp "${TMPDIR:-/tmp}/urweb.XXXXXXXXXX")
_hellof=$(mktemp "${TMPDIR:-/tmp}/urweb.XXXXXXXXXX")
printf '%s\n' "$_exp" > "$_expf"
printf '%s\n' "$_hello" > "$_hellof"
diff "$_expf" "$_hellof" || { rm -f "$_expf" "$_hellof"; kill $(cat "$TESTPID") 2>/dev/null; echo "FAIL: minimal-rust/hello"; exit 1; }
rm -f "$_expf" "$_hellof"
kill $(cat "$TESTPID") 2>/dev/null || true
echo "PASS: minimal-rust/hello"
