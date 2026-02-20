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
"$URWEB" -boot -noEmacs -endpoints "$TESTENDPOINTS" "$TEST" \
    || { printf 'FAIL [endpoints]: urweb compile failed\n' >&2; exit 1; }

"$TESTSRV" -q -a 127.0.0.1 &
printf '%s\n' "$!" > "$TESTPID"
sleep 1

cleanup() { kill "$(cat "$TESTPID" 2>/dev/null)" 2>/dev/null || true; }
trap cleanup EXIT

PREFIX="http://localhost:8080"

if command -v jq >/dev/null 2>&1; then
    # Parse endpoints JSON with jq
    jq -r '.endpoints[] | "\(.method) \(.url)"' "$TESTENDPOINTS" \
    | while IFS=' ' read -r method url; do
        full="$PREFIX/$url"
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
        full="$PREFIX/$url"
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
