#!/usr/bin/env bash
set -euo pipefail
track="$(cd "$(dirname "$0")" && pwd)"
base="$(cd "$track/.." && pwd)"
export PATH="$base/toolchain/lean-4.36.0-linux/bin:$PATH"
cd "$base/centered-cube/lean"
lake env bash -c 'export LEAN_PATH="$1/BE-port:$1:$LEAN_PATH"; cd "$1/BE-port"; set -e; for f in ProbabilityApproximation/{ChenShao/Leaves,Stein/IndicatorSolution,ChenShao/Concentration,ChenShao/UniformBerryEsseen}.lean; do lean -DautoImplicit=false -DrelaxedAutoImplicit=false -o "${f%.lean}.olean" "$f"; done; lean Axioms.lean; cd "$1"; lean -o BerryClosedCDF.olean BerryClosedCDF.lean' bash "$track"
