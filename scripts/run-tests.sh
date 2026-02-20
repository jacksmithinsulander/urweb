#!/bin/sh
# Run Ur/Web tests. Requires: bin/urweb (or build.ninja to build it), sqlite3, curl
# Optional: jq (for endpoints test), gcc (for cffi test)
set -e
TESTDB="${TESTDB:-/tmp/urweb.db}"
TESTPID="${TESTPID:-/tmp/urweb.pid}"
srcdir="${1:-.}"
builddir="${2:-.}"

URWEB="$(cd "$builddir" && pwd)/bin/urweb"
export URWEB

_ts() { date +%H:%M:%S 2>/dev/null || true; }

# Build compiler if missing
if [ ! -f "$URWEB" ]; then
  if [ -f "$builddir/build.ninja" ]; then
    echo "[$(_ts)] urweb compiler not found, building..."
    (cd "$builddir" && (samu bin/urweb 2>/dev/null || ninja bin/urweb)) || { echo "Failed to build urweb"; exit 1; }
  else
    echo "urweb compiler not found at $URWEB and no build.ninja to build it" >&2
    exit 1
  fi
fi

# Demo test
echo ""
echo "=== Demo test ==="
rm -f "$TESTDB"
echo "[$(_ts)] Building demo app..."
$URWEB -boot -noEmacs -dbms sqlite -db "$TESTDB" -demo /Demo demo
echo "[$(_ts)] Starting demo server..."
sqlite3 "$TESTDB" < "$srcdir/demo/demo.sql"
demo/demo.exe -q -a 127.0.0.1 & echo $! > "$TESTPID"
sleep 2
curl -s 'http://localhost:8080/Demo/Hello/main' | diff "$srcdir/tests/hello.html" - || { kill $(cat "$TESTPID") 2>/dev/null; echo "Test Hello failed"; exit 1; }
curl -s 'http://localhost:8080/Demo/Crud1/create?A=1&B=2&C=3&D=4' | diff "$srcdir/tests/crud1.html" - || { kill $(cat "$TESTPID") 2>/dev/null; echo "Test Crud1 failed"; exit 1; }
kill $(cat "$TESTPID") 2>/dev/null || true
echo "Demo test passed."

# Driver-based tests (each test has a .sh that is sourced by driver.sh after starting the app)
# Exclude: driver, lib (infra); cffi, endpoints, dbupload2 (standalone scripts)
testsdir="$srcdir/tests"
DRIVER_TESTS="aborter aborter2 agg align ascdesc attrs_escape bindpat bool both both2 case caseMod cdataF cdataL entities fact filter jsonTest utf8"
n=0
total_driver=18
echo ""
echo "=== Driver tests ($total_driver tests, ~15-30s each to compile) ==="
for base in $DRIVER_TESTS; do
  [ -f "$testsdir/$base.sh" ] || { echo "Warning: $base.sh missing, skipping"; continue; }
  n=$((n + 1))
  echo "[$(_ts)] [$n/$total_driver] $base"
  (cd "$testsdir" && URWEB="$URWEB" ./driver.sh "$base") || exit 1
done

# Standalone tests (own compile + server lifecycle)
echo ""
echo "=== Standalone tests (3) ==="
echo "[$(_ts)] [1/3] cffi"
(cd "$testsdir" && URWEB="$URWEB" ./cffi.sh) || exit 1
echo "[$(_ts)] [2/3] endpoints"
(cd "$testsdir" && URWEB="$URWEB" ./endpoints.sh) || exit 1
echo "[$(_ts)] [3/3] dbupload2"
(cd "$testsdir" && URWEB="$URWEB" ./dbupload2.sh) || exit 1

echo ""
echo "All tests passed."
