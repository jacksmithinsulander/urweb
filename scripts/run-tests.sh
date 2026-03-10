#!/bin/sh
# Run Ur/Web tests. Requires: bin/urweb (or build.ninja to build it), sqlite3, curl, node+npm
# Optional: jq (for endpoints test), gcc (for cffi test)
set -e
TESTDB="${TESTDB:-/tmp/urweb.db}"
TESTPID="${TESTPID:-/tmp/urweb.pid}"
srcdir="${1:-.}"
builddir="${2:-.}"

URWEB="$(cd "$builddir" && pwd)/bin/urweb"
URWEB_ARGS="${URWEB_ARGS:-}"
export URWEB URWEB_ARGS

_ts() { date +%H:%M:%S 2>/dev/null || true; }

# Build compiler if missing
if [ ! -f "$URWEB" ]; then
  if [ -f "$builddir/build.ninja" ]; then
    echo "[$(_ts)] urweb compiler not found, building..."
    (cd "$builddir" && (samu bin/urweb 2>/dev/null || ninja bin/urweb)) || { echo "Failed to build urweb"; exit 1; }
  else
    echo "FAIL: urweb compiler not found at $URWEB and no build.ninja to build it" >&2
    exit 1
  fi
fi

# Demo test
echo ""
echo "=== Demo test ==="
rm -f "$TESTDB"
echo "[$(_ts)] Building demo app (this may take a few minutes)..."
echo "  (output logged to $builddir/demo-build.log; if it hangs, inspect that file for last phase)"
( while sleep 20; do echo "  [$(_ts)] Still building demo app..."; done ) &
_demo_heartbeat=$!
( $URWEB $URWEB_ARGS -boot -noEmacs -dbms sqlite -db "$TESTDB" -demo /Demo "$srcdir/demo"
  echo $? > "$builddir/.demo_exit"
) 2>&1 | tee "$builddir/demo-build.log"
_exit=$(cat "$builddir/.demo_exit" 2>/dev/null || echo 1)
rm -f "$builddir/.demo_exit"
kill $_demo_heartbeat 2>/dev/null || true
wait $_demo_heartbeat 2>/dev/null || true
[ $_exit -eq 0 ] || { echo "FAIL: demo - build failed"; exit 1; }
echo "[$(_ts)] Demo build done. Starting demo server..."
# Free port 8080 in case a previous run left a server
_pid=$(lsof -ti:8080 2>/dev/null) || true
[ -n "$_pid" ] && kill $_pid 2>/dev/null || true
sleep 1
sqlite3 "$TESTDB" < "$srcdir/demo/demo.sql"
"$srcdir/demo/demo.exe" -q -a 127.0.0.1 & echo $! > "$TESTPID"
# Wait for demo server to be ready (up to 15s)
_dw=0
while [ $_dw -lt 15 ]; do
  curl -s 'http://127.0.0.1:8080/Demo/Hello/main' >/dev/null 2>/dev/null && break
  sleep 1
  _dw=$((_dw + 1))
done
[ $_dw -lt 15 ] || { kill $(cat "$TESTPID") 2>/dev/null; echo "FAIL: demo - server not ready after 15s"; exit 1; }
# Normalize: trim trailing newlines so diff doesn't fail on that alone
_hello=$(curl -s 'http://localhost:8080/Demo/Hello/main' | sed -e '$s/[[:space:]]*$//')
_exp=$(cat "$srcdir/tests/hello.html" | sed -e '$s/[[:space:]]*$//')
_expf=$(mktemp)
printf '%s\n' "$_exp" > "$_expf"
printf '%s\n' "$_hello" | diff - "$_expf" || { rm -f "$_expf"; kill $(cat "$TESTPID") 2>/dev/null; echo "FAIL: demo - Hello response mismatch"; exit 1; }
rm -f "$_expf"
curl -s 'http://localhost:8080/Demo/Crud1/create?A=1&B=2&C=3&D=4' | diff "$srcdir/tests/crud1.html" - || { kill $(cat "$TESTPID") 2>/dev/null; echo "FAIL: demo - Crud1 response mismatch"; exit 1; }
kill $(cat "$TESTPID") 2>/dev/null || true
echo "PASS: demo"

# Driver-based tests (each test has a .sh that is sourced by driver.sh after starting the app)
# Exclude: driver, lib (infra); cffi, endpoints, dbupload2 (standalone scripts)
testsdir="$srcdir/tests"
if [ -f "$testsdir/package.json" ]; then
  echo "[$(_ts)] Installing test deps (Playwright, may take 1–2 min)..."
  ( while sleep 30; do echo "  [$(_ts)] Still installing Playwright..."; done ) &
  _npm_heartbeat=$!
  (cd "$testsdir" && npm install && npx playwright install chromium) || { kill $_npm_heartbeat 2>/dev/null; echo "FAIL: Playwright install failed"; exit 1; }
  kill $_npm_heartbeat 2>/dev/null || true
  wait $_npm_heartbeat 2>/dev/null || true
  echo "[$(_ts)] Playwright ready."
fi
DRIVER_TESTS="aborter aborter2 agg align alert ascdesc attrMangle attrs_escape a_case_of_the_splits bindpat bodyClick bool both both2 button case caseMod ccheckbox cdataF cdataL cradio DynChannel entities fact filter jsonTest jsbspace utf8"
n=0
total_driver=27
echo ""
echo "=== Driver tests ($total_driver tests, ~15-30s each to compile) ==="
# Free driver test ports (8081-8107) before starting
for _p in 8081 8082 8083 8084 8085 8086 8087 8088 8089 8090 8091 8092 8093 8094 8095 8096 8097 8098 8099 8100 8101 8102 8103 8104 8105 8106 8107; do
  _pid=$(lsof -ti:$_p 2>/dev/null) || true
  [ -n "$_pid" ] && kill $_pid 2>/dev/null || true
done
sleep 2
for base in $DRIVER_TESTS; do
  [ -f "$testsdir/$base.sh" ] || { echo "Warning: $base.sh missing, skipping"; continue; }
  n=$((n + 1))
  echo "[$(_ts)] [$n/$total_driver] $base"
  (cd "$testsdir" && URWEB="$URWEB" PORT=$((8080 + n)) ./driver.sh "$base" $((8080 + n))) || exit 1
done

# Standalone tests (own compile + server lifecycle)
echo ""
echo "=== Standalone tests (5) ==="
echo "[$(_ts)] [1/5] cffi"
(cd "$testsdir" && URWEB="$URWEB" ./cffi.sh) || exit 1
echo "[$(_ts)] [2/5] endpoints"
(cd "$testsdir" && URWEB="$URWEB" ./endpoints.sh) || exit 1
echo "[$(_ts)] [3/5] dbupload2"
(cd "$testsdir" && URWEB="$URWEB" ./dbupload2.sh) || exit 1
echo "[$(_ts)] [4/5] new"
(cd "$testsdir" && URWEB="$URWEB" ./new.sh) || exit 1
echo "[$(_ts)] [5/5] install"
(cd "$testsdir" && URWEB="$URWEB" ./install.sh) || exit 1

echo ""
echo "PASS: all"
