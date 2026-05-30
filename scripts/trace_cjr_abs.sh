#!/bin/zsh
set -euo pipefail

export URWEB_DEBUG_CJR_ABS=1

./bin/urweb-rust -boot -noEmacs -dbms sqlite -db /tmp/urweb-cjr-abs.db demo/crud1 2>&1 \
  | rg 'URWEB_DEBUG_CJR_ABS|Anonymous function remains at code generation'
