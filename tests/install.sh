#!/bin/sh
# install.sh -- test 'urweb install' package manager
# Tests with a local fake package, then with urweb/upo from GitHub if online.
set -e

cd "$(dirname "$0")"
TESTNAME=install
. ./lib.sh

URWEB="${URWEB:-../bin/urweb}"
case "$URWEB" in /*) ;; *) URWEB="$(pwd)/$URWEB" ;; esac

TMPDIR="/tmp/urweb_install_test_$$"
cleanup() { rm -rf "$TMPDIR"; }
trap cleanup EXIT

mkdir -p "$TMPDIR"

# -----------------------------------------------------------------------
# Setup: create a fresh urweb project to install packages into
# -----------------------------------------------------------------------
cd "$TMPDIR"
"$URWEB" new installtest > /dev/null 2>&1
cd "$TMPDIR/installtest"

# Patch boot=true so the test binary finds its stdlib
sed 's/boot  = false/boot  = true/' urweb.toml > urweb.toml.tmp \
    && mv urweb.toml.tmp urweb.toml

# urweb install needs at least one git commit in the parent repo
git config user.email "test@example.com"
git config user.name  "Test"
git add .
git commit -q -m "initial"

# -----------------------------------------------------------------------
# Build a fake library package in a local git repo
# -----------------------------------------------------------------------
PKGDIR="$TMPDIR/fakepkg"
mkdir -p "$PKGDIR"
cd "$PKGDIR"
git init -q
git config user.email "test@example.com"
git config user.name  "Test"

# urweb.toml
printf '[package]\nname = "fakepkg"\nkind = "lib"\n\n[build]\nentry = "fakepkg"\nboot  = false\n' \
    > urweb.toml

# fakepkg.urs
printf 'val greet : string -> string\n' > fakepkg.urs

# fakepkg.ur
printf 'fun greet (name : string) : string = "Hello, " ^ name ^ "!"\n' > fakepkg.ur

# fakepkg.urp
printf 'fakepkg\n' > fakepkg.urp

git add .
git commit -q -m "initial"

# -----------------------------------------------------------------------
# Test 1: 'urweb install' with no package prints error
# -----------------------------------------------------------------------
cd "$TMPDIR/installtest"
"$URWEB" install > "$TMPDIR/out.txt" 2>&1 || true
grep -qi "requires\|usage\|package" "$TMPDIR/out.txt" \
    || fail "'urweb install' (no arg): expected usage error"

# -----------------------------------------------------------------------
# Test 2: 'urweb install' outside a project directory errors clearly
# -----------------------------------------------------------------------
cd "$TMPDIR"
"$URWEB" install fake/pkg > "$TMPDIR/out.txt" 2>&1 || true
grep -qi "urweb.toml" "$TMPDIR/out.txt" \
    || fail "'urweb install' (no project): expected urweb.toml error"

# -----------------------------------------------------------------------
# Test 3: 'urweb install <local-path>' installs the fake package
# -----------------------------------------------------------------------
cd "$TMPDIR/installtest"
"$URWEB" install "$PKGDIR" > "$TMPDIR/out.txt" 2>&1 \
    || fail "local install failed: $(cat "$TMPDIR/out.txt")"

# Submodule directory created
[ -d lib/fakepkg ] \
    || fail "install: lib/fakepkg/ not created"
[ -f lib/fakepkg/fakepkg.urp ] \
    || fail "install: lib/fakepkg/fakepkg.urp not found"

# .urp patched with library directive (entry from urweb.toml = fakepkg)
grep -q "library lib/fakepkg/fakepkg" installtest.urp \
    || fail "install: 'library lib/fakepkg/fakepkg' not added to installtest.urp"

# library directive is BEFORE the main module line
_lib_line=$(grep -n "library lib/fakepkg/fakepkg" installtest.urp | cut -d: -f1)
_mod_line=$(grep -n "^installtest$" installtest.urp | cut -d: -f1)
[ "$_lib_line" -lt "$_mod_line" ] \
    || fail "install: library directive must appear before main module in .urp"

# urweb.toml updated
grep -q "\[dependencies\]" urweb.toml \
    || fail "install: [dependencies] section not added to urweb.toml"
grep -q "fakepkg" urweb.toml \
    || fail "install: fakepkg not added to urweb.toml [dependencies]"

# -----------------------------------------------------------------------
# Test 4: installing the same package twice is rejected
# -----------------------------------------------------------------------
"$URWEB" install "$PKGDIR" > "$TMPDIR/out.txt" 2>&1 || true
grep -qi "already" "$TMPDIR/out.txt" \
    || fail "duplicate install: expected 'already installed' error"

# -----------------------------------------------------------------------
# Test 5: bad package spec is rejected
# -----------------------------------------------------------------------
"$URWEB" install "not/a/valid/github/spec" > "$TMPDIR/out.txt" 2>&1 || true
grep -qi "error\|cannot parse" "$TMPDIR/out.txt" \
    || fail "bad spec: expected parse error"

# -----------------------------------------------------------------------
# Test 6: 'urweb install urweb/upo' from GitHub
# Uses the real urweb/upo library (https://github.com/urweb/upo).
# Skipped if network is unavailable.
# -----------------------------------------------------------------------
_online=false
curl -sf --max-time 5 https://github.com > /dev/null 2>&1 && _online=true

if $_online; then
    # Fresh project so upo isn't already installed
    cd "$TMPDIR"
    "$URWEB" new upotest > /dev/null 2>&1
    cd "$TMPDIR/upotest"
    sed 's/boot  = false/boot  = true/' urweb.toml > urweb.toml.tmp \
        && mv urweb.toml.tmp urweb.toml
    git config user.email "test@example.com"
    git config user.name  "Test"
    git add .
    git commit -q -m "initial"

    "$URWEB" install urweb/upo > "$TMPDIR/upo_out.txt" 2>&1 \
        || fail "urweb/upo install failed: $(cat "$TMPDIR/upo_out.txt")"

    # upo cloned as submodule
    [ -d lib/upo ] \
        || fail "upo install: lib/upo/ not created"
    [ -f lib/upo/lib.urp ] \
        || fail "upo install: lib/upo/lib.urp not found (upo uses lib.urp as entry)"

    # library directive: since upo has no urweb.toml, falls back to 'library lib/upo'
    grep -q "library lib/upo" upotest.urp \
        || fail "upo install: 'library lib/upo' not added to upotest.urp"

    # urweb.toml updated
    grep -q "\[dependencies\]" urweb.toml \
        || fail "upo install: [dependencies] not in urweb.toml"
    grep -q '"lib/upo"' urweb.toml \
        || fail "upo install: upo path not in urweb.toml [dependencies]"

    # .gitmodules records the submodule
    [ -f .gitmodules ] \
        || fail "upo install: .gitmodules not created"
    grep -q "urweb/upo" .gitmodules \
        || fail "upo install: urweb/upo not in .gitmodules"

    printf '  (upo GitHub install: PASS)\n' >&2
else
    printf '  (skipping upo GitHub test: no network)\n' >&2
fi

printf 'PASS: install\n'
