#!/bin/sh
# Minimal test: compile demo/hello, run it, curl check. No full demo, no driver tests.
set -e
srcdir="${1:-.}"
builddir="${2:-.}"

URWEB="$(cd "$builddir" && pwd)/bin/urweb"
TESTDB="/tmp/urweb_minimal.db"
TESTPID="/tmp/urweb_minimal.pid"

# Free port 8080 in case a previous run left a server
_pid=$(lsof -ti:8080 2>/dev/null) || true
[ -n "$_pid" ] && kill $_pid 2>/dev/null || true
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
_expf=$(mktemp)
printf '%s\n' "$_exp" > "$_expf"
printf '%s\n' "$_hello" | diff - "$_expf" || { rm -f "$_expf"; kill $(cat "$TESTPID") 2>/dev/null; echo "FAIL: minimal/hello"; exit 1; }
rm -f "$_expf"
kill $(cat "$TESTPID") 2>/dev/null || true
echo "PASS: minimal/hello"
