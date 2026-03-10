#!/bin/sh
# endpoints.sh -- compile with -endpoints, start server, hit every endpoint.
set -e

cd "$(dirname "$0")"

TEST=endpoints
TESTPID="/tmp/uw_${TEST}.pid"
TESTENDPOINTS="/tmp/${TEST}.json"
TESTSRV="./${TEST}.exe"

rm -f "$TESTENDPOINTS" "$TESTPID" "$TESTSRV"

URWEB="${URWEB:-../bin/urweb}"
"$URWEB" ${URWEB_ARGS:+$URWEB_ARGS }-boot -noEmacs -endpoints "$TESTENDPOINTS" "$TEST" \
    || { printf 'FAIL [endpoints]: urweb compile failed\n' >&2; exit 1; }

PORT=${PORT:-8110}
# Free port in case a previous run left a server
_pid=$(lsof -ti:$PORT 2>/dev/null) || true
[ -n "$_pid" ] && kill $_pid 2>/dev/null || true
sleep 1

"$TESTSRV" -q -a 127.0.0.1 -p "$PORT" &
printf '%s\n' "$!" > "$TESTPID"
# Wait for server to be ready (up to 15s)
_wait=0
while [ $_wait -lt 15 ]; do
  (nc -z 127.0.0.1 "$PORT" 2>/dev/null || curl -s "http://127.0.0.1:$PORT/" >/dev/null 2>/dev/null) && break
  sleep 1
  _wait=$((_wait + 1))
done
[ $_wait -lt 15 ] || { printf 'FAIL [endpoints]: server not ready after 15s\n' >&2; exit 1; }

cleanup() { kill "$(cat "$TESTPID" 2>/dev/null)" 2>/dev/null || true; }
trap cleanup EXIT

PREFIX="http://localhost:$PORT"

if command -v jq >/dev/null 2>&1; then
    # Parse endpoints JSON with jq
    jq -r '.endpoints[] | "\(.method) \(.url)"' "$TESTENDPOINTS" \
    | while IFS=' ' read -r method url; do
        case "$url" in /*) full="$PREFIX$url" ;; *) full="$PREFIX/$url" ;; esac
        case $method in
            GET)
                curl -fs "$full" >/dev/null \
                    || { printf 'FAIL [endpoints]: GET %s failed\n' "$url" >&2; exit 1; }
                ;;
            POST)
                curl -fs -d "Nam=X&Msg=message&Sameday=on" "$full" >/dev/null \
                    || { printf 'FAIL [endpoints]: POST %s failed\n' "$url" >&2; exit 1; }
                ;;
        esac
    done
else
    # Fallback: awk-based JSON parser (handles simple flat arrays)
    awk '
        /"method"/ { gsub(/.*"method": *"|".*/, ""); method = $0 }
        /"url"/    { gsub(/.*"url": *"|"[,}]*.*/, ""); url = $0 }
        url && method {
            print method " " url
            method = ""; url = ""
        }
    ' "$TESTENDPOINTS" \
    | while IFS=' ' read -r method url; do
        case "$url" in /*) full="$PREFIX$url" ;; *) full="$PREFIX/$url" ;; esac
        case $method in
            GET)
                curl -fs "$full" >/dev/null \
                    || { printf 'FAIL [endpoints]: GET %s failed\n' "$url" >&2; exit 1; }
                ;;
            POST)
                curl -fs -d "Nam=X&Msg=message&Sameday=on" "$full" >/dev/null \
                    || { printf 'FAIL [endpoints]: POST %s failed\n' "$url" >&2; exit 1; }
                ;;
        esac
    done
fi

printf 'PASS: endpoints\n'
