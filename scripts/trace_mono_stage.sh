#!/bin/zsh
set -euo pipefail

export URWEB_DEBUG_MONO_STAGE=1

./bin/urweb-rust -boot -noEmacs -dbms sqlite -db /tmp/urweb-stage-trace.db demo/crud1 2>&1 \
  | rg 'URWEB_DEBUG_MONO_STAGE'
