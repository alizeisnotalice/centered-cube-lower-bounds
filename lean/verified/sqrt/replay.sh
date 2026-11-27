#!/usr/bin/env bash
set -euo pipefail
root="$(cd -- "$(dirname -- "$0")" && pwd)"
cd "$root"
: "${LEAN_BIN:=lean}"
: "${MATHLIB_LEAN_PATH:?Set to the Lean 4.36.0 Mathlib fc4f59e dependency paths, without project oleans}"
tmp="$(mktemp -d)"
trap 'rm -rf -- "$tmp"' EXIT
"$LEAN_BIN" --version
export LEAN_PATH="$tmp:$MATHLIB_LEAN_PATH"
while IFS= read -r module; do
  mp="${module//./\/}"
  mkdir -p "$tmp/$(dirname "$mp")"
  printf '\n=== %s ===\n' "$module"
  "$LEAN_BIN" -j1 -o "$tmp/$mp.olean" "$mp.lean"
done < MODULES.txt
printf '\n=== ExactManuscriptAudit ===\n'
"$LEAN_BIN" -j1 -o "$tmp/ExactManuscriptAudit.olean" ExactManuscriptAudit.lean
