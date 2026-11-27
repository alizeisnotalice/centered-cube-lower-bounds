/-
Wiring the `√n/log n` endgame.

`Cubes.sqrtLog_of_truncated_halo` proves: given, at a fixed dimension `n`,
a truncated test function `g` with the manuscript's mass `(2n²)ⁿ`, a set `E` of
measure at least `(c/log n)(2n²-2)ⁿ`, and a pointwise cube witness on `E` at
height `e^h` with `h ≥ log n / 2 - 5/2`, one gets
`C_n ≥ c e^{-5/2}/2 · √n/log n`.

This file performs the quantifier assembly: if such data exist for every
sufficiently large integer `n` (with one fixed `c > 0`), then the top-level
statement `SqrtLogLowerBound` of `Cubes.lean` holds.  The analytic content that
produces the data (uniform moderate deviations, scale correlations, periodic
superlevel measure) is *not* proved here; it is exactly the remaining gap, and
it enters only through the hypothesis `hdata`.
-/
import Cubes

open Set MeasureTheory
open scoped ENNReal NNReal

namespace CenteredCube

/-- The halo data of the `√n/log n` manuscript at dimension `n`. -/
structure HaloData (n : ℕ) (c : ℝ) : Type where
  /-- height exponent `h = u²/2 - 2` -/
  height : ℝ
  /-- the periodic tensor test function, before truncation -/
  test : Space n → ℝ
  /-- the superlevel set on the torus -/
  halo : Set (Space n)
  height_ge : Real.log (n : ℝ) / 2 - 5 / 2 ≤ height
  integrable : Integrable ((box n ((n : ℝ) ^ 2)).indicator test) volume
  mass : absMass ((box n ((n : ℝ) ^ 2)).indicator test) =
    ENNReal.ofReal ((2 * (n : ℝ) ^ 2) ^ n)
  volume_ge : ENNReal.ofReal ((c / Real.log (n : ℝ)) * (2 * (n : ℝ) ^ 2 - 2) ^ n) ≤
    volume halo
  witness : ∀ x ∈ halo, x ∈ box n ((n : ℝ) ^ 2 - 1) ∧
    ∃ r : ℝ, 0 < r ∧ r ≤ 2 ∧
      ENNReal.ofReal (Real.exp height) < cubeAverage test x r

/-- **Assembly of the `√n/log n` theorem.**  If the manuscript's halo data exist
for every integer `n ≥ N₀` with a fixed `c > 0`, then `C_n ≥ c' √n/log n`
eventually, with `c' = c e^{-5/2}/2 > 0`; this is `SqrtLogLowerBound`. -/
theorem sqrtLogLowerBound_of_haloData {c : ℝ} (hc : 0 < c) {N₀ : ℕ}
    (hdata : ∀ n : ℕ, N₀ ≤ n → HaloData n c) : SqrtLogLowerBound := by
  refine ⟨c * Real.exp (-(5 / 2)) / 2, by positivity, max N₀ 2, ?_⟩
  intro n hn
  have hnN : N₀ ≤ n := le_trans (le_max_left _ _) hn
  have hn2 : 2 ≤ n := le_trans (le_max_right _ _) hn
  obtain ⟨h, g, E, hheight, hf, hmass, hvol, hE⟩ := hdata n hnN
  exact sqrtLog_of_truncated_halo hn2 hc hheight g E hf hmass hvol hE

end CenteredCube

#print axioms CenteredCube.sqrtLogLowerBound_of_haloData
