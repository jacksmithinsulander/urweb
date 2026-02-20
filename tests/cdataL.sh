# Follow the two links; each leads to a page with cdata-quoted text
href1=$(nth_href CdataL/main 1)
href2=$(nth_href CdataL/main 2)
[ -n "$href1" ] || fail "CdataL/main: could not find first link"
[ -n "$href2" ] || fail "CdataL/main: could not find second link"
check "$href1" "&lt;Hi."
check "$href2" "Bye."
