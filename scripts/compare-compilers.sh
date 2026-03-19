#!/bin/sh
# Compare ML (bin/urweb) vs Rust (bin/urweb-rust) compiler output.
#
# Compiles demo/hello.urp with both compilers, producing application
# executables.  Diffs are shown for:
#   1. Defined symbols  (nm -U | sort)
#   2. Generated C source
#   3. Generated SQL schema
#
# Colourised output when colordiff(1) or GNU diff --color is available.

set -e
srcdir="${1:-.}"
builddir="${2:-.}"

URWEB_ML="$builddir/bin/urweb"
URWEB_RUST="$builddir/bin/urweb-rust"
URP="$srcdir/demo/hello.urp"
PROJECT="$srcdir/demo/hello"
OUTDIR="$builddir/compare"

mkdir -p "$OUTDIR"

ML_EXE="$OUTDIR/ml_hello"
RUST_EXE="$OUTDIR/rust_hello"
ML_C="$OUTDIR/ml_hello.c"
RUST_C="$OUTDIR/rust_hello.c"
ML_SQL="$OUTDIR/ml_schema.sql"
RUST_SQL="$OUTDIR/rust_schema.sql"
ML_NM="$OUTDIR/ml_hello.nm"
RUST_NM="$OUTDIR/rust_hello.nm"

# ── Colour helper ─────────────────────────────────────────────────────────────
pretty_diff() {
    local label="$1" a="$2" b="$3"
    printf "\n══════════════════════════════════════════════════════\n"
    printf "  diff: %s\n" "$label"
    printf "══════════════════════════════════════════════════════\n"
    if diff -u "$a" "$b" > "$OUTDIR/diff_${label}.txt" 2>/dev/null; then
        printf "  ✓  identical\n"
        return
    fi
    if command -v colordiff > /dev/null 2>&1; then
        colordiff -u "$a" "$b" || true
    elif diff --color=always -u "$a" "$b" > /dev/null 2>&1; then
        diff --color=always -u "$a" "$b" || true
    else
        diff -u "$a" "$b" || true
    fi
}

# ── Compile with ML compiler ──────────────────────────────────────────────────
printf "\n── Compiling demo/hello with ML compiler ──────────────────\n"
(cd "$builddir" && \
    "$URWEB_ML" -boot -noEmacs -dbms sqlite -db /tmp/compare_ml.db \
        -sql "$ML_SQL" -o "$ML_EXE" "$PROJECT" 2>/dev/null \
) || {
    echo "FAIL: ML compiler failed on demo/hello" >&2; exit 1
}
# -debug flag writes C source to /tmp/webapp.c
(cd "$builddir" && \
    "$URWEB_ML" -debug -boot -noEmacs -dbms sqlite -db /tmp/compare_ml.db \
        -sql /dev/null "$PROJECT" > /dev/null 2>/dev/null \
) && cp /tmp/webapp.c "$ML_C" 2>/dev/null || true
[ -f "$ML_SQL" ] || touch "$ML_SQL"
printf "  exe: %s\n" "$ML_EXE"
printf "  C:   %s\n" "$ML_C"
printf "  SQL: %s\n" "$ML_SQL"

# ── Compile with Rust compiler ────────────────────────────────────────────────
printf "\n── Compiling demo/hello with Rust compiler ─────────────────\n"
"$URWEB_RUST" -boot -o "$RUST_EXE" "$URP" 2>/dev/null || {
    echo "FAIL: Rust compiler failed on demo/hello" >&2; exit 1
}
# Try dump_output example for C/SQL side-channel
if ! [ -f "$RUST_C" ]; then
    (cd "$srcdir" && cargo run --example dump_output --release -- \
        "$URP" "$RUST_C" "$RUST_SQL" 2>/dev/null) || true
fi
[ -f "$RUST_SQL" ] || touch "$RUST_SQL"
printf "  exe: %s\n" "$RUST_EXE"
printf "  C:   %s\n" "$RUST_C"
printf "  SQL: %s\n" "$RUST_SQL"

# ── Diffs ─────────────────────────────────────────────────────────────────────

# 1. Symbol table (nm)
if [ -f "$ML_EXE" ] && [ -f "$RUST_EXE" ]; then
    nm -U "$ML_EXE"   2>/dev/null | awk '{print $NF}' | sort > "$ML_NM"   || true
    nm -U "$RUST_EXE" 2>/dev/null | awk '{print $NF}' | sort > "$RUST_NM" || true
    pretty_diff "symbols" "$ML_NM" "$RUST_NM"
fi

# 2. Generated C source
if [ -f "$ML_C" ] && [ -f "$RUST_C" ]; then
    pretty_diff "C_source" "$ML_C" "$RUST_C"
else
    printf "\n  (skipping C source diff — one or both .c files missing)\n"
fi

# 3. SQL schema
if [ -f "$ML_SQL" ] && [ -f "$RUST_SQL" ]; then
    pretty_diff "SQL_schema" "$ML_SQL" "$RUST_SQL"
fi

# ── Summary ───────────────────────────────────────────────────────────────────
printf "\n── Summary ─────────────────────────────────────────────────\n"
for f in "$OUTDIR"/diff_*.txt; do
    [ -f "$f" ] || continue
    label=$(basename "$f" .txt | sed 's/^diff_//')
    if [ -s "$f" ]; then
        lines=$(wc -l < "$f" | tr -d ' ')
        printf "  %-22s  DIFFERS  (%d diff lines)\n" "$label" "$lines"
    else
        printf "  %-22s  identical\n" "$label"
    fi
done
printf "\nFull diffs saved to %s/\n" "$OUTDIR"
