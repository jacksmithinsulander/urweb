# tests/lib.sh -- shared helpers sourced by driver.sh and individual test scripts
# Not executable on its own; source with: . ./lib.sh

PORT=${PORT:-8080}

# fail MSG -- print failure and exit
fail() {
    printf 'FAIL [%s]: %s\n' "${TESTNAME:-?}" "$*" >&2
    exit 1
}

# _url_full PATH -- resolve relative/absolute path to full URL
_url_full() {
    case $1 in
        http://*|https://*) printf '%s' "$1" ;;
        /*)                  printf 'http://localhost:%s%s' "$PORT" "$1" ;;
        *)                   printf 'http://localhost:%s/%s' "$PORT" "$1" ;;
    esac
}

# check PATH TEXT -- assert curl response contains TEXT
check() {
    _full=$(_url_full "$1")
    curl -fs "$_full" | grep -qF "$2" || fail "GET $1: expected: $2"
}

# check_re PATH PATTERN -- assert curl response matches ERE pattern
check_re() {
    _full=$(_url_full "$1")
    curl -fs "$_full" | grep -qE "$2" || fail "GET $1: expected pattern: $2"
}

# check_absent PATH TEXT -- assert curl response does NOT contain TEXT
check_absent() {
    _full=$(_url_full "$1")
    curl -fs "$_full" | grep -qF "$2" && fail "GET $1: should not contain: $2" || true
}

# check_xpath PATH XPATH [EXPECTED_TEXT] -- assert XPath matches at least one node (uses Playwright)
# Caller must run from tests/ (driver.sh does this).
check_xpath() {
    _full=$(_url_full "$1")
    _xpath="$2"
    _expected="${3-}"
    if [ -n "$_expected" ]; then
        node ./playwright-check.js "$_full" "$_xpath" "$_expected" || fail "GET $1: xpath $_xpath: $3"
    else
        node ./playwright-check.js "$_full" "$_xpath" || fail "GET $1: xpath $_xpath matched nothing"
    fi
}

# run_playwright TESTNAME -- run interactive Playwright test (clicks, alerts, etc.)
# Test module: playwright-tests/<TESTNAME>.js exports async (page, baseUrl) => void
run_playwright() {
    _base="http://localhost:$PORT"
    node ./playwright-run.js "$1" "$_base" || fail "Playwright test $1 failed"
}

# nth_href PAGE_PATH N -- extract Nth anchor href from page (1-indexed)
nth_href() {
    _full=$(_url_full "$1")
    curl -fs "$_full" \
        | sed 's/<a /\n<a /g' \
        | grep '^<a ' \
        | sed -n "${2}s/.*href=\"\([^\"]*\)\".*/\1/p"
}

# post_form PAGE_PATH FIELD=VALUE... EXPECTED_TEXT
# GETs PAGE_PATH, extracts the first form action + __uwsig, POSTs with fields.
post_form() {
    _url=$1; _fields=$2; _expected=$3
    _full=$(_url_full "$_url")
    _page=$(curl -fs "$_full")
    _action=$(printf '%s' "$_page" \
        | sed -n 's/.*<form[^>]* action="\([^"]*\)".*/\1/p' | head -1)
    _sig=$(printf '%s' "$_page" \
        | sed -n 's/.*name="__uwsig"[^>]* value="\([^"]*\)".*/\1/p' | head -1)
    [ -n "$_action" ] || fail "post_form $1: no form action found"
    [ -n "$_sig"    ] || fail "post_form $1: no __uwsig found"
    _result=$(curl -fs \
        --data-urlencode "__uwsig=$_sig" \
        -d "$_fields" \
        "http://localhost:$PORT$_action")
    printf '%s' "$_result" | grep -qF "$_expected" \
        || fail "POST $1 -> $_action: expected: $3"
}

# post_form_n PAGE_PATH NTH_FORM FIELD=VALUE... EXPECTED_TEXT
# Like post_form but picks the Nth form on the page (1-indexed).
post_form_n() {
    _url=$1; _nth=$2; _fields=$3; _expected=$4
    _full=$(_url_full "$_url")
    _page=$(curl -fs "$_full")
    _action=$(printf '%s' "$_page" \
        | sed 's/<form /\n<form /g' \
        | grep '^<form ' \
        | sed -n "${_nth}s/.*action=\"\([^\"]*\)\".*/\1/p")
    _sig=$(printf '%s' "$_page" \
        | sed 's/<input /\n<input /g' \
        | grep 'name="__uwsig"' \
        | sed -n "${_nth}s/.*value=\"\([^\"]*\)\".*/\1/p")
    [ -n "$_action" ] || fail "post_form_n $1 form $2: no action found"
    [ -n "$_sig"    ] || fail "post_form_n $1 form $2: no __uwsig found"
    _result=$(curl -fs \
        --data-urlencode "__uwsig=$_sig" \
        -d "$_fields" \
        "http://localhost:$PORT$_action")
    printf '%s' "$_result" | grep -qF "$_expected" \
        || fail "POST $1 form $2 -> $_action: expected: $4"
}
