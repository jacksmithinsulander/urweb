# Follow the first two links from the main page
href1=$(nth_href Bool/main 1)
href2=$(nth_href Bool/main 2)
[ -n "$href1" ] || fail "Bool/main: could not find first link"
[ -n "$href2" ] || fail "Bool/main: could not find second link"
check "$href1" "Yes!"
check "$href2" "No!"
