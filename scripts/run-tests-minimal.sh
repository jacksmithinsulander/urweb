#!/bin/sh
# Minimal test: compile demo/hello, run it, curl check. No full demo, no driver tests.
set -e
srcdir="${1:-.}"
builddir="${2:-.}"

URWEB="$(cd "$builddir" && pwd)/bin/urweb"
TESTDB="/tmp/urweb_minimal.db"
TESTPID="/tmp/urweb_minimal.pid"
. "$srcdir/tests/lib.sh"

# Free port 8080 in case a previous run left a server
free_port 8080
sleep 1

if [ ! -f "$URWEB" ]; then
  [ -f "$builddir/build.ninja" ] || { echo "FAIL: minimal - urweb not found and no build.ninja"; exit 1; }
  (cd "$builddir" && (samu bin/urweb 2>/dev/null || ninja bin/urweb)) || { echo "FAIL: minimal - could not build urweb"; exit 1; }
fi

rm -f "$TESTDB" "$TESTPID"
echo "=== Minimal test: demo/hello ==="
"$URWEB" -boot -noEmacs -dbms sqlite -db "$TESTDB" "$srcdir/demo/hello" 2>/dev/null || { echo "FAIL: minimal/compile"; exit 1; }
echo "PASS: minimal/compile"
"$srcdir/demo/hello.exe" -q -a 127.0.0.1 & echo $! > "$TESTPID"
sleep 1
# Normalize: trim trailing newlines so diff doesn't fail on that alone
_hello=$(curl -s 'http://localhost:8080/Hello/main' | sed -e '$s/[[:space:]]*$//')
_exp=$(cat "$srcdir/tests/hello.html" | sed -e '$s/[[:space:]]*$//')
_expf=$(mktemp "${TMPDIR:-/tmp}/urweb.XXXXXXXXXX")
_hellof=$(mktemp "${TMPDIR:-/tmp}/urweb.XXXXXXXXXX")
printf '%s\n' "$_exp" > "$_expf"
printf '%s\n' "$_hello" > "$_hellof"
diff "$_expf" "$_hellof" || { rm -f "$_expf" "$_hellof"; kill $(cat "$TESTPID") 2>/dev/null; echo "FAIL: minimal/hello"; exit 1; }
rm -f "$_expf" "$_hellof"
kill $(cat "$TESTPID") 2>/dev/null || true
echo "PASS: minimal/hello"
