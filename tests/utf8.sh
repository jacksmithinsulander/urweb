# Each subtest page renders one or more <pre> elements that must all say "True"
no_falses() {
    _path=$1
    _body=$(curl -fs "http://localhost:$PORT/$_path")
    [ -n "$_body" ] || fail "$_path: empty response"
    printf '%s' "$_body" | grep -q '<pre>' || fail "$_path: no <pre> elements found"
    printf '%s' "$_body" | grep '<pre>' | grep -qvF '>True<' \
        && fail "$_path: found a non-True value"
    return 0
}

# For full-range tests the page body must be empty (no error output)
full_test() {
    _name=$1
    gap=1000; i=0
    while [ "$((i + gap))" -lt 130000 ]; do
        _body=$(curl -fs "http://localhost:$PORT/Utf8/$_name/$i/$((i + gap))")
        [ -z "$(printf '%s' "$_body" | sed 's/<[^>]*>//g' | tr -d ' \t\n')" ] \
            || fail "Utf8/$_name/$i/$((i + gap)): non-empty body: $_body"
        i=$((i + gap))
    done
}

no_falses Utf8/substrings
no_falses Utf8/strlens
no_falses Utf8/strlenGens
no_falses Utf8/strcats
no_falses Utf8/strsubs
no_falses Utf8/strsuffixs
no_falses Utf8/strchrs
no_falses Utf8/strindexs
no_falses Utf8/strsindexs
no_falses Utf8/strcspns
no_falses Utf8/str1s
no_falses Utf8/isalnums
no_falses Utf8/isalphas
no_falses Utf8/isblanks
no_falses Utf8/iscntrls
no_falses Utf8/isdigits
no_falses Utf8/isgraphs
no_falses Utf8/islowers
no_falses Utf8/isprints
no_falses Utf8/ispuncts
no_falses Utf8/isspaces
no_falses Utf8/isuppers
no_falses Utf8/isxdigits
no_falses Utf8/touppers
no_falses Utf8/ord_and_chrs
no_falses Utf8/test_db

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
