# All no_falses pages are checked via Playwright (they use client-side rendering)
run_playwright utf8

# For full-range tests: check server handles all codepoints without crashing
full_test() {
    _name=$1
    gap=1000; i=0
    while [ "$((i + gap))" -lt 130000 ]; do
        _code=$(curl -so /dev/null -w "%{http_code}" "http://localhost:$PORT/Utf8/$_name/$i/$((i + gap))")
        [ "$_code" = "200" ] \
            || fail "Utf8/$_name/$i/$((i + gap)): HTTP $_code"
        i=$((i + gap))
    done
}


full_test ftTolower
full_test ftToupper
full_test ftIsalpha
full_test ftIsdigit
full_test ftIsalnum
full_test ftIsspace
full_test ftIsblank
full_test ftIsprint
full_test ftIsxdigit
full_test ftIsupper
full_test ftIslower
