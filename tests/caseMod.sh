href1=$(nth_href CaseMod/main 1)
href2=$(nth_href CaseMod/main 2)
href3=$(nth_href CaseMod/main 3)
[ -n "$href1" ] || fail "CaseMod/main: could not find link 1"
[ -n "$href2" ] || fail "CaseMod/main: could not find link 2"
[ -n "$href3" ] || fail "CaseMod/main: could not find link 3"
check "$href1" "C A"
check "$href1" "Again!"
check "$href2" "C B"
check "$href2" "Again!"
check "$href3" "D"
check "$href3" "Again!"
