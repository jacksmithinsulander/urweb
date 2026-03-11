#!/bin/sh
# Compare ML (bin/urweb) vs Rust (bin/urweb-rust) compiler output.
# Compiles demo/hello with both, captures generated C and SQL, and diffs them.
# Goal: the compilers should produce equivalent (ideally identical) output.
set -e
srcdir="${1:-.}"
builddir="${2:-.}"

URWEB_ML="$builddir/bin/urweb"
URWEB_RUST="$builddir/bin/urweb-rust"
PROJECT="$srcdir/demo/hello"
OUTDIR="$builddir/compare"
ML_C="$OUTDIR/ml_webapp.c"
ML_SQL="$OUTDIR/ml_schema.sql"
RUST_C="$OUTDIR/rust_webapp.c"
RUST_SQL="$OUTDIR/rust_schema.sql"

mkdir -p "$OUTDIR"

# Ensure ML compiler exists
if [ ! -f "$URWEB_ML" ]; then
  echo "Building ML compiler..."
  (cd "$builddir" && (samu bin/urweb 2>/dev/null || ninja bin/urweb)) || {
    echo "FAIL: ML compiler (bin/urweb) not found and could not build" >&2
    exit 1
  }
fi

# Ensure Rust compiler exists
if [ ! -f "$URWEB_RUST" ]; then
  echo "Building Rust compiler..."
  (cd "$builddir" && (samu urweb-rust 2>/dev/null || ninja urweb-rust)) || {
    echo "FAIL: Rust compiler (bin/urweb-rust) not found and could not build" >&2
    exit 1
  }
fi

echo "=== Compare compilers: demo/hello ==="

# ML: compile with -debug (writes to /tmp/webapp.c) and -sql for schema
echo "Compiling with ML compiler..."
(cd "$builddir" && "$URWEB_ML" -debug -boot -noEmacs -dbms sqlite -db /tmp/compare_ml.db -sql "$ML_SQL" "$PROJECT" 2>/dev/null) || {
  echo "FAIL: ML compiler failed on $PROJECT" >&2
  exit 1
}
if [ -f /tmp/webapp.c ]; then
  cp /tmp/webapp.c "$ML_C"
else
  echo "FAIL: ML compiler -debug did not produce /tmp/webapp.c" >&2
  exit 1
fi
[ -f "$ML_SQL" ] || touch "$ML_SQL"

# Rust: use dump_output example
echo "Compiling with Rust compiler (dump_output)..."
URP_PATH="$srcdir/demo/hello.urp"
(cd "$srcdir" && cargo run --example dump_output --release -- "$URP_PATH" "$RUST_C" "$RUST_SQL" 2>/dev/null) || {
  echo "FAIL: Rust dump_output failed on $PROJECT" >&2
  echo "  (Rust compiler may not yet support full demo/hello)" >&2
  exit 1
}

# Diff C output
echo ""
echo "--- Diff: C output (ML vs Rust) ---"
if diff "$ML_C" "$RUST_C" > "$OUTDIR/diff_c.txt" 2>/dev/null; then
  echo "PASS: C output identical"
else
  echo "C output differs (see $OUTDIR/diff_c.txt)"
  head -100 "$OUTDIR/diff_c.txt"
fi

# Diff SQL output
echo ""
echo "--- Diff: SQL output (ML vs Rust) ---"
if diff "$ML_SQL" "$RUST_SQL" > "$OUTDIR/diff_sql.txt" 2>/dev/null; then
  echo "PASS: SQL output identical"
else
  echo "SQL output differs (see $OUTDIR/diff_sql.txt)"
  head -50 "$OUTDIR/diff_sql.txt"
fi

echo ""
echo "Outputs saved to $OUTDIR/"
