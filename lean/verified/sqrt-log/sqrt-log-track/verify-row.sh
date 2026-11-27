#!/usr/bin/env bash
set -euo pipefail
track="$(cd "$(dirname "$0")" && pwd)"
base="$(cd "$track/.." && pwd)"
bash "$track/verify-berry.sh"
export PATH="$base/toolchain/lean-4.36.0-linux/bin:$PATH"
cd "$base/centered-cube/lean"
lake env bash -c 'set -e; cd "$1"; export LEAN_PATH="$1/BE-port:$1:$LEAN_PATH"; for f in ProductTilt TiltedMoments TiltedBerryRow IidLawTransfer StandardizedLength MDWindow RateError; do lean -o "$f.olean" "$f.lean"; done' bash "$track"
