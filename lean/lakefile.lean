import Lake
open Lake DSL

/-
Reproducible build target for the two centred-cube lower-bound formalizations.

Pinned: Lean 4.36.0 (see `lean-toolchain`), Mathlib v4.36.0
(commit fc4f59e577feb1a4956671bc04ac18aaaf8cd842, see `lake-manifest.json`).

`lake build` elaborates `All.lean`, which imports every module below; each module
re-runs its own `#print axioms` diagnostics when elaborated.
-/
package «centered-cube-lower-bounds» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.36.0"

lean_lib «LowerBounds»
lean_lib «Cubes»
lean_lib «LogTensor»
lean_lib «RudinShapiro»
lean_lib «Model»
lean_lib «Coefficients»
lean_lib «Trig»
lean_lib «Abel»
lean_lib «CosineForm»
lean_lib «Average»
lean_lib «Periodic»
lean_lib «Product»
lean_lib «Variance»
lean_lib «RhoNormalise»
lean_lib «SqrtLimit»
lean_lib «SqrtLogWiring»

@[default_target]
lean_lib «All»
