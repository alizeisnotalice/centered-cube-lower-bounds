#!/usr/bin/env bash
# Reproduce the build from a clean checkout of the branch.
#
#   ./clean-checkout.sh [<branch>]
#
# Two modes:
#  * if $MATHLIB_PACKAGES points at an existing `.lake/packages` directory of the
#    same Mathlib revision (v4.36.0, fc4f59e…), it is symlinked in, so no network
#    access and no recompilation of Mathlib is needed (this is what was done when
#    `clean-checkout.log` was produced);
#  * otherwise the script runs `lake exe cache get`, which downloads the pinned
#    Mathlib oleans (needs network, several GB on first use).
set -eu
branch="${1:-lean/round2-20261127}"
here="$(cd "$(dirname "$0")" && pwd)"
repo="$(cd "$here/../.." && pwd)"
dest="${TMPDIR:-/tmp}/cc-lb-clean-$$"

git clone -q --branch "$branch" "$repo" "$dest"
cd "$dest/lean"
mkdir -p .lake
if [ -n "${MATHLIB_PACKAGES:-}" ] && [ -d "${MATHLIB_PACKAGES}" ]; then
  ln -sfn "$MATHLIB_PACKAGES" .lake/packages
else
  export PATH="$HOME/.elan/bin:$PATH"
  lake exe cache get
fi
export PATH="$HOME/.elan/bin:$PATH"
lake build
echo "clean checkout built at $dest"
