#!/bin/sh
# driver.sh -- compile an Ur/Web test app, run its shell test, then clean up.
# Usage: ./driver.sh <testname> [PORT]
set -e

Name=$1
PORT=${2:-8080}
cd "$(dirname "$0")"

URWEB="${URWEB:-../bin/urweb}"
TESTDB="/tmp/uw_${Name}.db"
TESTSQL="/tmp/uw_${Name}.sql"
TESTPID="/tmp/uw_${Name}.pid"
TESTSRV="./${Name}.exe"

rm -f "$TESTDB" "$TESTSQL" "$TESTPID" "$TESTSRV"

printf '  compiling...' >&2
"$URWEB" -boot -noEmacs -dbms sqlite -db "$TESTDB" -sql "$TESTSQL" "$Name" \
    || { printf ' FAIL\n' >&2; printf 'FAIL [%s]: urweb compile failed\n' "$Name" >&2; exit 1; }
printf ' run...' >&2

[ -f "$TESTSQL" ] && sqlite3 "$TESTDB" < "$TESTSQL"

"$TESTSRV" -q -a 127.0.0.1 -p "$PORT" &
printf '%s\n' "$!" > "$TESTPID"
sleep 1

cleanup() {
    kill "$(cat "$TESTPID" 2>/dev/null)" 2>/dev/null || true
    rm -f "$TESTPID" "$TESTSRV"
}
trap cleanup EXIT

TESTNAME=$Name
export PORT TESTNAME
. ./lib.sh
. ./"${Name}.sh"

printf ' ok\n' >&2
printf 'PASS: %s\n' "$Name"
