#!/usr/bin/env bash
# Re-elaborate every module from source and capture the `#print axioms` report.
# Usage: ./verify.sh   (from this directory; requires `lake build` to have run once
# so that the Mathlib oleans and the sibling modules are on the search path.)
set -u
cd "$(dirname "$0")/../../lean" || exit 1
export PATH="$HOME/.elan/bin:$PATH"
out="../verification/lean-20261127/axioms.txt"
: > "$out"
status=0
for f in LowerBounds Cubes LogTensor RudinShapiro Model Coefficients Trig Abel RhoNormalise Variance SqrtLimit SqrtLogWiring All; do
  echo "=== $f.lean ===" >> "$out"
  if lake env lean "$f.lean" >> "$out" 2>&1; then
    echo "[ok] $f" >&2
  else
    echo "[FAIL] $f" >&2
    status=1
  fi
done
echo "--- sorryAx occurrences:" >> "$out"
grep -c "^'.*sorryAx" "$out" >> "$out" || true
exit $status
