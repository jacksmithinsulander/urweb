#!/bin/sh
# Run Ur/Web tests. Requires: bin/urweb, sqlite3, curl
set -e
TESTDB="${TESTDB:-/tmp/urweb.db}"
TESTPID="${TESTPID:-/tmp/urweb.pid}"
srcdir="${1:-.}"
builddir="${2:-.}"

URWEB="$(cd "$builddir" && pwd)/bin/urweb"
export URWEB

# Demo test
echo "=== Demo test ==="
rm -f "$TESTDB"
$URWEB -boot -noEmacs -dbms sqlite -db "$TESTDB" -demo /Demo demo
sqlite3 "$TESTDB" < "$srcdir/demo/demo.sql"
demo/demo.exe -q -a 127.0.0.1 & echo $! > "$TESTPID"
sleep 1
curl -s 'http://localhost:8080/Demo/Hello/main' | diff "$srcdir/tests/hello.html" - || { kill $(cat "$TESTPID") 2>/dev/null; echo "Test Hello failed"; exit 1; }
curl -s 'http://localhost:8080/Demo/Crud1/create?A=1&B=2&C=3&D=4' | diff "$srcdir/tests/crud1.html" - || { kill $(cat "$TESTPID") 2>/dev/null; echo "Test Crud1 failed"; exit 1; }
kill $(cat "$TESTPID") 2>/dev/null || true
echo "Demo test passed."

# Driver-based tests (tests/*.sh except driver.sh and lib.sh)
echo "=== Driver tests ==="
testsdir="$srcdir/tests"
for sh in "$testsdir"/*.sh; do
  base=$(basename "$sh" .sh)
  case "$base" in
    driver|lib) continue ;;
    *)
      echo "Running $base..."
      (cd "$testsdir" && URWEB="$URWEB" ./driver.sh "$base") || exit 1
      ;;
  esac
done

echo "All tests passed."
