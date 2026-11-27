#!/usr/bin/env bash
set -euo pipefail
track="$(cd "$(dirname "$0")" && pwd)"
base="$(cd "$track/.." && pwd)"
export PATH="$base/toolchain/lean-4.36.0-linux/bin:$PATH"
cd "$base/centered-cube/lean"
lake env bash -c 'set -e; cd "$1"; export LEAN_PATH="$1:$2:$1/BE-port:$LEAN_PATH"; for f in GoodEvent PointThreshold PointGrowth ActualGood ActualGrowth HitProduct TensorAverage PairGrowth; do lean -j2 -o "$f.olean" "$f.lean"; done' bash "$track" "$base/geometry"
