#!/bin/zsh
set -euo pipefail

export URWEB_DEBUG_CJR_TOP_LAMBDA=1

./bin/urweb-rust -boot -noEmacs -dbms sqlite -db /tmp/urweb-cjr-top.db demo/crud1 2>&1 \
  | rg 'URWEB_DEBUG_CJR_TOP|Anonymous function remains at code generation'
