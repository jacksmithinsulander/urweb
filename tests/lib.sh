# tests/lib.sh -- shared helpers sourced by driver.sh and individual test scripts
# Not executable on its own; source with: . ./lib.sh

PORT=${PORT:-8080}

# _maybe_strip_app_prefix PATH -- /Foo/bar -> /bar, otherwise empty
_maybe_strip_app_prefix() {
    case $1 in
        /*/*)
            _rest=${1#/}
            _rest=${_rest#*/}
            [ -n "$_rest" ] && printf '/%s' "$_rest"
            ;;
    esac
}

# _http_code URL -- best-effort HTTP status (000 on transport failure)
_http_code() {
    curl -s -o /dev/null -w '%{http_code}' "$1" 2>/dev/null || printf '000'
}

# _resolve_local_url PATH -- prefer given path, but fall back from /Foo/bar to /bar on 404
_resolve_local_url() {
    case $1 in
        /*) _path=$1 ;;
        *)  _path="/$1" ;;
    esac

    _base="http://localhost:$PORT"
    _full="$_base$_path"
    _code=$(_http_code "$_full")

    if [ "$_code" = "404" ]; then
        _alt_path=$(_maybe_strip_app_prefix "$_path")
        if [ -n "$_alt_path" ]; then
            _alt="$_base$_alt_path"
            _alt_code=$(_http_code "$_alt")
            if [ "$_alt_code" != "404" ] && [ "$_alt_code" != "000" ]; then
                printf '%s' "$_alt"
                return
            fi
        fi
    fi

    printf '%s' "$_full"
}

# free_port PORT -- kill process listening on PORT (uses lsof when available, else no-op)
free_port() {
    _p=$1
    _pid=''
    if command -v lsof >/dev/null 2>&1; then
        _pid=$(lsof -ti:$_p 2>/dev/null) || true
    fi
    [ -n "$_pid" ] && kill $_pid 2>/dev/null || true
}

# wait_for_port PORT [MAX_SEC] -- return 0 when HTTP server on PORT is ready (curl or nc)
wait_for_port() {
    _port=$1
    _max=${2:-15}
    _i=0
    while [ $_i -lt $_max ]; do
        if curl -s "http://127.0.0.1:$_port/" >/dev/null 2>/dev/null; then
            return 0
        fi
        if command -v nc >/dev/null 2>&1 && nc -z 127.0.0.1 $_port 2>/dev/null; then
            return 0
        fi
        sleep 1
        _i=$((_i + 1))
    done
    return 1
}

# fail MSG -- print failure and exit
fail() {
    printf 'FAIL [%s]: %s\n' "${TESTNAME:-?}" "$*" >&2
    exit 1
}

# _url_full PATH -- resolve relative/absolute path to full URL
_url_full() {
    case $1 in
        http://*|https://*) printf '%s' "$1" ;;
        *)                   _resolve_local_url "$1" ;;
    esac
}

# check PATH TEXT -- assert curl response contains TEXT
check() {
    _full=$(_url_full "$1")
    curl -s "$_full" | grep -qF "$2" || fail "GET $1: expected: $2"
}

# check_re PATH PATTERN -- assert curl response matches ERE pattern
check_re() {
    _full=$(_url_full "$1")
    curl -s "$_full" | grep -qE "$2" || fail "GET $1: expected pattern: $2"
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
# GETs PAGE_PATH, extracts the first form action + Sig (if present), POSTs with fields.
post_form() {
    _url=$1; _fields=$2; _expected=$3
    _full=$(_url_full "$_url")
    _page=$(curl -fs "$_full")
    _action=$(printf '%s' "$_page" \
        | sed -n 's/.*<form[^>]* action="\([^"]*\)".*/\1/p' | head -1)
    _sig=$(printf '%s' "$_page" \
        | sed -n 's/.*name="Sig" value="\([^"]*\)".*/\1/p' | head -1)
    [ -n "$_action" ] || fail "post_form $1: no form action found"
    if [ -n "$_sig" ]; then
        _result=$(curl -fs \
            --data-urlencode "Sig=$_sig" \
            -d "$_fields" \
            "http://localhost:$PORT$_action")
    else
        _result=$(curl -fs \
            -d "$_fields" \
            "http://localhost:$PORT$_action")
    fi
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
        | grep 'name="Sig"' \
        | sed -n "${_nth}s/.*value=\"\([^\"]*\)\".*/\1/p")
    [ -n "$_action" ] || fail "post_form_n $1 form $2: no action found"
    if [ -n "$_sig" ]; then
        _result=$(curl -s \
            --data-urlencode "Sig=$_sig" \
            -d "$_fields" \
            "http://localhost:$PORT$_action" || true)
    else
        _result=$(curl -s \
            -d "$_fields" \
            "http://localhost:$PORT$_action" || true)
    fi
    printf '%s' "$_result" | grep -qF "$_expected" \
        || fail "POST $1 form $2 -> $_action: expected: $4"
}
