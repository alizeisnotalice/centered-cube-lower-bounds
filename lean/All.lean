/-
Build root for the centred-cube lower-bound formalization.

Layout
-----
* `Cubes`, `LogTensor`, `RudinShapiro` — byte-identical copies of the verified
  2026-11-27 snapshot in `sqrt-log-20261127/` (see `REUSE.sha256`).
* `Model`      — the operator/constant definitions and their equivalence with the
  manuscript's definition (1.1) of `C_n`.
* `Abel`       — Rudin–Shapiro density: Abel summation, the `15√K` weighted bound,
  pointwise bounds and normalisation data for `ρ_K`.
* `SqrtLimit`  — the `√n` manuscript: transfer from "every `b < C_*`" to `liminf`,
  the explicit constant `87/(220√(58π))`, and the `√n/35` corollary.
-/
import LowerBounds
import Cubes
import LogTensor
import RudinShapiro
import Model
import Coefficients
import Trig
import Abel
import Variance
import RhoNormalise
import SqrtLimit
import SqrtLogWiring
