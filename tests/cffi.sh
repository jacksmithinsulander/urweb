#!/bin/sh
# cffi.sh -- compile C helper, then compile+run the Ur/Web cffi test
set -e

cd "$(dirname "$0")"
. ./lib.sh

Name=cffi
TESTDB="/tmp/uw_${Name}.db"
TESTSQL="/tmp/uw_${Name}.sql"
TESTPID="/tmp/uw_${Name}.pid"
TESTSRV="./${Name}.exe"
TESTNAME=$Name

rm -f "$TESTDB" "$TESTSQL" "$TESTPID" "$TESTSRV"

# Compile the C helper library
${CC:-gcc} -pthread -Wimplicit -Werror -Wno-unused-value \
    -I ../include/urweb \
    -c test.c -o test.o -g

# Compile the Ur/Web app
URWEB="${URWEB:-../bin/urweb}"
"$URWEB" -boot -noEmacs -dbms sqlite -db "$TESTDB" -sql "$TESTSQL" "$Name" \
    || { printf 'FAIL [%s]: urweb compile failed\n' "$Name" >&2; exit 1; }

[ -f "$TESTSQL" ] && sqlite3 "$TESTDB" < "$TESTSQL"

PORT=${PORT:-8080}
export PORT
"$TESTSRV" -q -a 127.0.0.1 -p "$PORT" &
printf '%s\n' "$!" > "$TESTPID"
sleep 1

cleanup() { kill "$(cat "$TESTPID" 2>/dev/null)" 2>/dev/null || true; }
trap cleanup EXIT

# test 1: form 1 triggers JS button alerts
run_playwright cffi

# test 2: submit form 2 (xact) -> "All good."
post_form_n "Cffi/main" 2 "" "All good."

# test 3: submit form 3 (xact2 + error) -> fatal error page
post_form_n "Cffi/main" 3 "" "Fatal error"

printf 'PASS: %s\n' "$Name"
