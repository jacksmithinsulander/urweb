#!/bin/sh
# new.sh -- test 'urweb new' and 'urweb build' for app and library scaffolding
set -e

cd "$(dirname "$0")"
TESTNAME=new
. ./lib.sh

URWEB="${URWEB:-../bin/urweb}"
# Convert to absolute path since we cd into temp dirs below
case "$URWEB" in /*) ;; *) URWEB="$(pwd)/$URWEB" ;; esac

PORT="${PORT:-8080}"
TMPDIR="/tmp/urweb_new_test_$$"

cleanup() {
    kill "$(cat "$TMPDIR/app.pid" 2>/dev/null)" 2>/dev/null || true
    rm -rf "$TMPDIR"
}
trap cleanup EXIT

mkdir -p "$TMPDIR"
cd "$TMPDIR"

# --- Test 1: 'urweb new' without a name prints an error ---
"$URWEB" new > out.txt 2>&1 || true
grep -q "project name" out.txt \
    || fail "'urweb new' (no name): expected error mentioning 'project name'"

# --- Test 2: bad project name (contains hyphen) is rejected ---
"$URWEB" new "bad-name" > out.txt 2>&1 || true
grep -qi "error" out.txt \
    || fail "bad name 'bad-name': expected an error message"
[ ! -d "bad-name" ] \
    || fail "bad name 'bad-name': directory should not have been created"

# --- Test 3: bad project name (starts with digit) is rejected ---
"$URWEB" new "3app" > out.txt 2>&1 || true
grep -qi "error" out.txt \
    || fail "bad name '3app': expected an error message"
[ ! -d "3app" ] \
    || fail "bad name '3app': directory should not have been created"

# --- Test 4: 'urweb new myapp' creates an app project ---
"$URWEB" new myapp > out.txt 2>&1
grep -q "Created app 'myapp'" out.txt \
    || fail "'urweb new myapp': expected 'Created app' in output"

# urweb.toml
[ -f myapp/urweb.toml ] \
    || fail "app: urweb.toml not created"
grep -q 'kind.*=.*"app"' myapp/urweb.toml \
    || fail "app urweb.toml: missing kind = \"app\""
grep -q 'entry.*=.*"myapp"' myapp/urweb.toml \
    || fail "app urweb.toml: missing entry = \"myapp\""
grep -q 'db' myapp/urweb.toml \
    || fail "app urweb.toml: missing db field"
grep -q 'ccompiler' myapp/urweb.toml \
    || fail "app urweb.toml: missing ccompiler field"
grep -q '\[style\]' myapp/urweb.toml \
    || fail "app urweb.toml: missing [style] section"
grep -q 'scss' myapp/urweb.toml \
    || fail "app urweb.toml: missing scss field"
grep -q 'css' myapp/urweb.toml \
    || fail "app urweb.toml: missing css field"

# .urp includes css directive
[ -f myapp/myapp.urp ] \
    || fail "app: myapp/myapp.urp not created"
grep -q "file /style/css/main.css" myapp/myapp.urp \
    || fail "app .urp: missing 'file /style/css/main.css' directive"

# .ur
[ -f myapp/myapp.ur ] \
    || fail "app: myapp/myapp.ur not created"
[ ! -f myapp/myapp.urs ] \
    || fail "app: myapp/myapp.urs should not exist for an app"
grep -q "transaction page" myapp/myapp.ur \
    || fail "app .ur: missing 'transaction page' type annotation"
grep -q "source 0" myapp/myapp.ur \
    || fail "app .ur: missing 'source 0' (counter source)"
grep -q "Count:" myapp/myapp.ur \
    || fail "app .ur: missing 'Count:' label"
grep -q "button" myapp/myapp.ur \
    || fail "app .ur: missing button elements"
grep -q "stylesheet" myapp/myapp.ur \
    || fail "app .ur: missing CSS <link rel=stylesheet>"

# style directory
[ -f myapp/style/scss/main.scss ] \
    || fail "app: style/scss/main.scss not created"
[ -f myapp/style/css/main.css ] \
    || fail "app: style/css/main.css not created (pre-compiled CSS)"
grep -qF '$primary' myapp/style/scss/main.scss \
    || fail "app scss: missing \$primary variable"
grep -q '&:hover' myapp/style/scss/main.scss \
    || fail "app scss: missing &:hover nesting"
grep -q '#3498db' myapp/style/css/main.css \
    || fail "app css: missing compiled color #3498db"

# AI context files
[ -f myapp/cursor.md ] \
    || fail "app: cursor.md not created"
[ -f myapp/claude.md ] \
    || fail "app: claude.md not created"
grep -q "Ur/Web" myapp/cursor.md \
    || fail "app cursor.md: missing Ur/Web content"
grep -q "Ur/Web" myapp/claude.md \
    || fail "app claude.md: missing Ur/Web content"

# .gitignore
[ -f myapp/.gitignore ] \
    || fail "app: .gitignore not created"
grep -q '\.exe' myapp/.gitignore \
    || fail "app .gitignore: missing *.exe"
grep -q '\.db' myapp/.gitignore \
    || fail "app .gitignore: missing *.db"
grep -q 'style/css' myapp/.gitignore \
    || fail "app .gitignore: missing style/css entry (compiled CSS should be gitignored)"

# git repo
if command -v git >/dev/null 2>&1; then
    [ -d myapp/.git ] \
        || fail "app: .git directory not initialized"
fi

# --- Test 5: 'urweb build' from inside the app project ---
# Patch boot=true so the test binary finds its stdlib
sed 's/boot  = false/boot  = true/' myapp/urweb.toml > myapp/urweb.toml.tmp \
    && mv myapp/urweb.toml.tmp myapp/urweb.toml
cd "$TMPDIR/myapp"
"$URWEB" build > "$TMPDIR/build_out.txt" 2>&1 \
    || fail "'urweb build': failed (output: $(cat "$TMPDIR/build_out.txt"))"
[ -f myapp.exe ] \
    || fail "'urweb build': myapp.exe not produced"
cd "$TMPDIR"

# --- Test 6: app serves a page with Counter heading and buttons ---
"$TMPDIR/myapp/myapp.exe" -q -a 127.0.0.1 -p "$PORT" &
echo $! > app.pid
sleep 1
_page=$(curl -s "http://localhost:$PORT/Myapp/main")
printf '%s' "$_page" | grep -q "Counter" \
    || fail "app serve: response missing 'Counter' heading"
printf '%s' "$_page" | grep -q "<button" \
    || fail "app serve: response missing '<button' elements"
kill "$(cat app.pid 2>/dev/null)" 2>/dev/null || true

# --- Test 7: 'urweb new' on an existing directory is rejected ---
cd "$TMPDIR"
"$URWEB" new myapp > out.txt 2>&1 || true
grep -qi "already exists\|error" out.txt \
    || fail "existing dir: expected error when project dir already exists"

# --- Test 8: 'urweb new --lib mylib' creates a library project ---
"$URWEB" new --lib mylib > out.txt 2>&1
grep -q "Created library 'mylib'" out.txt \
    || fail "'urweb new --lib mylib': expected 'Created library' in output"

# urweb.toml
[ -f mylib/urweb.toml ] \
    || fail "library: urweb.toml not created"
grep -q 'kind.*=.*"lib"' mylib/urweb.toml \
    || fail "library urweb.toml: missing kind = \"lib\""
grep -q 'entry.*=.*"mylib"' mylib/urweb.toml \
    || fail "library urweb.toml: missing entry = \"mylib\""
grep -qv '\[style\]' mylib/urweb.toml \
    || fail "library urweb.toml: should not have [style] section"

# files
[ -f mylib/mylib.urp ] \
    || fail "library: mylib/mylib.urp not created"
[ -f mylib/mylib.ur ] \
    || fail "library: mylib/mylib.ur not created"
[ -f mylib/mylib.urs ] \
    || fail "library: mylib/mylib.urs not created"
grep -q "val add" mylib/mylib.urs \
    || fail "library .urs: missing 'val add'"
grep -q "val greet" mylib/mylib.urs \
    || fail "library .urs: missing 'val greet'"

# no style directory for libraries
[ ! -d mylib/style ] \
    || fail "library: style/ directory should not be created for a library"

# git repo
if command -v git >/dev/null 2>&1; then
    [ -d mylib/.git ] \
        || fail "library: .git directory not initialized"
fi

# --- Test 9: 'urweb build' type-checks the library ---
sed 's/boot  = false/boot  = true/' mylib/urweb.toml > mylib/urweb.toml.tmp \
    && mv mylib/urweb.toml.tmp mylib/urweb.toml
cd "$TMPDIR/mylib"
"$URWEB" build > "$TMPDIR/build_lib_out.txt" 2>&1 \
    || fail "'urweb build' (library): failed (output: $(cat "$TMPDIR/build_lib_out.txt"))"
cd "$TMPDIR"

# --- Test 10: 'urweb build' outside a project dir errors clearly ---
"$URWEB" build > out.txt 2>&1 || true
grep -qi "urweb.toml" out.txt \
    || fail "'urweb build' (no toml): expected error mentioning urweb.toml"

printf 'PASS: new\n'
