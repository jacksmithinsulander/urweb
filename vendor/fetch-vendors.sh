#!/bin/sh
# Fetch vendored dependencies for building Ur/Web.
#
# Submodules: BearSSL (TLS/crypto), samurai (ninja-compatible build tool)
# This script initializes all submodules when in a git repo. When not in a git repo
# (e.g. tarball), only samurai can be cloned; BearSSL and 9front require git submodules.

set -e

cd "${0%/*}"
rootdir="$(cd .. && pwd)"

if test -d "$rootdir/.git" && git -C "$rootdir" rev-parse --git-dir >/dev/null 2>&1; then
  echo "  Initializing submodules..."
  git -C "$rootdir" submodule update --init --recursive
else
  # No git (e.g. tarball): clone BearSSL and samurai
  if test -d BearSSL; then
    echo "  BearSSL: already present"
  else
    echo "  Cloning BearSSL..."
    git clone --depth 1 "https://www.bearssl.org/git/BearSSL" BearSSL
  fi
  if test -d samurai; then
    echo "  samurai: already present"
  else
    echo "  Cloning samurai..."
    git clone --depth 1 "https://github.com/michaelforney/samurai.git" samurai
  fi
fi

echo ""
echo "Vendors ready. Build BearSSL with: make -C vendor/BearSSL (configure does this automatically)"
echo "Build samurai with: make -C vendor/samurai (if not using system samurai)"
echo "Then run ./configure from the project root."
