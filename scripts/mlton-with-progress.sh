#!/bin/sh
# Run MLton with periodic "still compiling" progress messages.
# Usage: mlton-with-progress.sh [mlton args...]
# MLton produces no output until done; this script prints status every 30s.
set -e

flagfile=$(mktemp)
rm -f "$flagfile"
touch "$flagfile"
cleanup() { rm -f "$flagfile"; }
trap cleanup EXIT

# Progress loop: runs until flagfile is removed (when MLton finishes)
( while [ -f "$flagfile" ] 2>/dev/null; do sleep 30; [ -f "$flagfile" ] 2>/dev/null || exit 0; printf '  [%s] ... still compiling\n' "$(date +%H:%M:%S)"; done ) &

echo ""
printf '[%s] Compiling Ur/Web compiler with MLton (2-3 min)...\n' "$(date +%H:%M:%S)"
"$@" || { rm -f "$flagfile"; exit 1; }
rm -f "$flagfile"
sleep 1  # let progress loop notice and exit cleanly
printf '[%s] Compiler build complete.\n' "$(date +%H:%M:%S)"
echo ""
