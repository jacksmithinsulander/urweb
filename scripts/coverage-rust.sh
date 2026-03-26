#!/bin/sh
# Generate Rust test coverage in lcov format and enforce 100% line coverage.
# Requires: cargo-llvm-cov (install with: cargo install cargo-llvm-cov)
#   On Rust 1.81 use: cargo install cargo-llvm-cov --version 0.6.21
#   On Rust 1.87+ use: cargo install cargo-llvm-cov
#
# Outputs: lcov.info (and optionally HTML under target/llvm-cov/html)
set -e
cd "$(dirname "$0")/.."

if ! cargo llvm-cov --version >/dev/null 2>&1; then
  echo "error: cargo-llvm-cov not found. Install with:" >&2
  echo "  cargo install cargo-llvm-cov   # Rust 1.87+" >&2
  echo "  cargo install cargo-llvm-cov --version 0.6.21   # Rust 1.81" >&2
  exit 1
fi

# Run tests with coverage, emit lcov, require 100% line coverage
cargo llvm-cov test \
  --lcov \
  --output-path lcov.info \
  --fail-under-lines 100

echo "Coverage: 100% (lcov.info written)"
