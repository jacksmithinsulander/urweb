#!/bin/sh
# Minimal test: compile demo/hello, run it, curl check. No full demo, no driver tests.
set -e
srcdir="${1:-.}"
builddir="${2:-.}"

URWEB="$(cd "$builddir" && pwd)/bin/urweb"
TESTDB="/tmp/urweb_minimal.db"
TESTPID="/tmp/urweb_minimal.pid"

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
curl -s 'http://localhost:8080/Hello/main' | diff "$srcdir/tests/hello.html" - || { kill $(cat "$TESTPID") 2>/dev/null; echo "FAIL: minimal/hello"; exit 1; }
kill $(cat "$TESTPID") 2>/dev/null || true
echo "PASS: minimal/hello"
