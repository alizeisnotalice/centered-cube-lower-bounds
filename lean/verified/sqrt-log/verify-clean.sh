#!/usr/bin/env bash
set -euo pipefail
root="$(cd "$(dirname "$0")" && pwd)"
export PATH="$root/toolchain/lean-4.36.0-linux/bin:$PATH"
printf 'Toolchain: '; lean --version
cd "$root/centered-cube/lean"
printf 'Mathlib pinned git HEAD: '; git -C .lake/packages/mathlib rev-parse HEAD
lake build
bash "$root/sqrt-log-track/verify-g4.sh"
mapfile -t mods < "$root/geometry-order.txt"
export LEAN_PATH="$root/geometry:$root/sqrt-log-track:$root/sqrt-log-track/BE-port:$PWD/.lake/build/lib/lean:$(printf '%s:' "$PWD"/.lake/packages/*/.lake/build/lib/lean)"
cd "$root/geometry"
for m in ${mods[0]}; do
  echo "=== $m ==="
  lean -j2 -o "$m.olean" "$m.lean"
done
bash "$root/sqrt-log-track/verify-onepoint.sh"
for m in ${mods[1]} FinalAudit; do
  echo "=== $m ==="
  lean -j2 -o "$m.olean" "$m.lean"
done
