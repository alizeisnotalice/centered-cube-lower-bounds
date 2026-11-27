#!/usr/bin/env bash
set -euo pipefail
track="$(cd "$(dirname "$0")" && pwd)"
base="$(cd "$track/.." && pwd)"
bash "$track/verify-row.sh"
export PATH="$base/toolchain/lean-4.36.0-linux/bin:$PATH"
cd "$base/centered-cube/lean"
lake env bash -c 'set -e; cd "$1"; export LEAN_PATH="$1/BE-port:$1:$LEAN_PATH"; for f in CGFThird CGFTaylor NormalizedSaddle TiltTransfer GaussianStrip NormalTailTransfer ModerateNumeric ModerateDeviation ModerateDeviationIidLaw; do lean -o "$f.olean" "$f.lean"; done' bash "$track"
