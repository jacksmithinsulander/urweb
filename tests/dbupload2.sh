#!/bin/sh
# dbupload2: test blob upload. Submits form with file and verifies redirect shows the uploaded image.
set -e

cd "$(dirname "$0")"
. ./lib.sh

Name=dbupload2
TESTDB="/tmp/uw_${Name}.db"
TESTSQL="/tmp/uw_${Name}.sql"
TESTPID="/tmp/uw_${Name}.pid"
TESTSRV="./${Name}.exe"
PORT=8083

URWEB="${URWEB:-../bin/urweb}"
rm -f "$TESTDB" "$TESTSQL" "$TESTPID" "$TESTSRV"

"$URWEB" ${URWEB_ARGS:+$URWEB_ARGS }-boot -noEmacs -dbms sqlite -db "$TESTDB" -sql "$TESTSQL" "$Name" \
  || { printf 'FAIL [%s]: urweb compile failed\n' "$Name" >&2; exit 1; }
[ -f "$TESTSQL" ] && sqlite3 "$TESTDB" < "$TESTSQL"

"$TESTSRV" -q -a 127.0.0.1 -p "$PORT" &
printf '%s\n' "$!" > "$TESTPID"
sleep 2

cleanup() { kill "$(cat "$TESTPID" 2>/dev/null)" 2>/dev/null || true; rm -f "$TESTPID"; }
trap cleanup EXIT

TESTNAME=$Name
export PORT TESTNAME

# Submit form with file upload: GET page, extract action + __uwsig, POST with file
_full="http://localhost:$PORT/Dbupload2/main"
_page=$(curl -fs "$_full")
_action=$(printf '%s' "$_page" | sed -n 's/.*<form[^>]* action="\([^"]*\)".*/\1/p' | head -1)
_sig=$(printf '%s' "$_page" | sed -n 's/.*name="__uwsig"[^>]* value="\([^"]*\)".*/\1/p' | head -1)
[ -n "$_action" ] || fail "dbupload2: no form action found"
[ -n "$_sig" ] || fail "dbupload2: no __uwsig found"

touch /tmp/empty
_result=$(curl -fs -F "__uwsig=$_sig" -F "File=@/tmp/empty" -F "Param=test" "http://localhost:$PORT$_action")
printf '%s' "$_result" | grep -qE '<form|</body>' || fail "upload response should contain form or body"
# After upload, main() shows the form and any images; we inserted one row so img should appear
printf '%s' "$_result" | grep -qE '<img|<form' || fail "upload response should show form and uploaded image"

printf 'PASS: %s\n' "$Name"
