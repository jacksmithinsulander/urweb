#!/bin/sh
# Test that Ur/Web compiles demo/hello with gcc, clang, and cproc (C11 compliant).
# Usage: ./scripts/test-cc-compilers.sh [srcdir] [builddir]
set -e

srcdir="${1:-.}"
builddir="${2:-.}"
URWEB="${URWEB:-$builddir/bin/urweb}"
TESTDB="/tmp/urweb_cc_test.db"

[ -f "$URWEB" ] || { echo "FAIL: urweb not found at $URWEB"; exit 1; }

run_with_cc() {
    _cc="$1"
    _name="$2"
    printf "  Testing with %s... " "$_name"
    rm -f "$srcdir/demo/hello.exe" "$TESTDB"
    if "$URWEB" -boot -noEmacs -dbms sqlite -db "$TESTDB" -ccompiler "$_cc" "$srcdir/demo/hello" 2>/dev/null; then
        [ -x "$srcdir/demo/hello.exe" ] || { echo "FAIL (exe not produced)"; return 1; }
        echo "ok"
        return 0
    else
        echo "FAIL (compile failed)"
        return 1
    fi
}

echo "=== CC compiler tests (C11 compliance) ==="
failed=0

if command -v gcc >/dev/null 2>&1; then
    run_with_cc "gcc" "gcc" || failed=1
else
    echo "  Skipping gcc (not found)"
fi

if command -v clang >/dev/null 2>&1; then
    run_with_cc "clang" "clang" || failed=1
else
    echo "  Skipping clang (not found)"
fi

CPROC="$builddir/vendor/cproc/cproc"
[ -x "$CPROC" ] || CPROC="$srcdir/vendor/cproc/cproc"
[ -x "$CPROC" ] || CPROC=""
if [ -n "$CPROC" ]; then
    if command -v qbe >/dev/null 2>&1; then
        run_with_cc "$CPROC" "cproc" || failed=1
    else
        echo "  Skipping cproc (QBE not installed; brew install qbe)"
    fi
elif command -v cproc >/dev/null 2>&1 && command -v qbe >/dev/null 2>&1; then
    run_with_cc "cproc" "cproc (system)" || failed=1
else
    echo "  Skipping cproc (not built; samu cproc, needs QBE: brew install qbe)"
fi

[ $failed -eq 0 ] && echo "PASS: all available C compilers" || { echo "FAIL: some C compiler tests failed"; exit 1; }
