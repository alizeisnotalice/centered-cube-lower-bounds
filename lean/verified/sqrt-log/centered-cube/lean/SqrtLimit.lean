/-
The `√n` manuscript: from "every `b < C_*`" to the limit inferior.

Theorem 1.1 of the manuscript states
`liminf_{n→∞} C_n/√n ≥ C_* = 87/(220√(58π)) > 1/35`,
the limit inferior being taken over all positive integer dimensions.

The analytic work of the manuscript (periodic narrow peaks indexed by
finite-field labels, positive spectral compensation, exponential tilting and a
Brownian crossing estimate) is not formalized here.  What this file does close is
the *purely order-theoretic and numerical* part of the manuscript, which is the
part the paper itself treats as bookkeeping:

* `Cstar` is defined and `1/35 < Cstar` is proved in `ℝ` from the explicit
  Mathlib bound `π < 3.1416` (`Cstar_gt_one_div_35`);
* the equivalence between the "`∀ b < C_*`, eventually `C_n ≥ b√n`" form and the
  `liminf` statement (`liminf_sqrt_ge`), including the `ℝ≥0∞ → ℝ` handling;
* the passage from the limit inferior to "`C_n ≥ √n/35` for every sufficiently
  large integer `n`" (`sqrt_div_35_eventually`), with the quantifier over all
  integers `n ≥ N` rather than a subsequence of dimensions.

Nothing here assumes a periodic model, a lattice model, or a restricted scale
range: `weakConstant` is the constant of `Cubes.lean` throughout.
-/
import Cubes
import Model
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Order.LiminfLimsup

open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace CenteredCube

/-- The explicit constant of the `√n` manuscript, `C_* = 87/(220√(58π))`. -/
noncomputable def Cstar : ℝ := 87 / (220 * Real.sqrt (58 * Real.pi))

theorem Cstar_pos : 0 < Cstar := by
  unfold Cstar
  positivity

/-- `C_* > 1/35`, proved from `π < 3.1416` by rational arithmetic only. -/
theorem Cstar_gt_one_div_35 : (1 / 35 : ℝ) < Cstar := by
  have hpi : Real.pi < 3.1416 := Real.pi_lt_d4
  have hsq : 58 * Real.pi < (13.6 : ℝ) ^ 2 := by nlinarith
  have hsqrt : Real.sqrt (58 * Real.pi) < 13.6 := by
    rw [Real.sqrt_lt' (by norm_num)]
    exact hsq
  have hden : 220 * Real.sqrt (58 * Real.pi) < 3045 := by nlinarith
  have hpos : (0 : ℝ) < 220 * Real.sqrt (58 * Real.pi) := by positivity
  unfold Cstar
  rw [lt_div_iff₀ hpos]
  nlinarith

/-- The `liminf` form of the main theorem, derived from the manuscript's
"for every `b < C_*`" form.  The hypothesis is stated with `ℝ≥0∞` multiplication
so that no finiteness of `C_n` is needed; the conclusion is the literal
`liminf_{n} C_n/√n ≥ C_*`. -/
theorem liminf_sqrt_ge
    (h : ∀ b : ℝ, b < Cstar → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ENNReal.ofReal b * ENNReal.ofReal (Real.sqrt n) ≤ weakConstant n) :
    ENNReal.ofReal Cstar ≤
      Filter.liminf (fun n : ℕ => weakConstant n / ENNReal.ofReal (Real.sqrt n)) Filter.atTop := by
  rw [le_liminf_iff]
  intro y hy
  have hyfin : y ≠ ∞ := ne_top_of_lt (hy.trans_le le_top)
  have hyC : y.toReal < Cstar := by
    have h1 : y.toReal < (ENNReal.ofReal Cstar).toReal :=
      (ENNReal.toReal_lt_toReal hyfin ENNReal.ofReal_ne_top).mpr hy
    simpa [ENNReal.toReal_ofReal Cstar_pos.le] using h1
  obtain ⟨b, hyb, hbC⟩ : ∃ b : ℝ, y.toReal < b ∧ b < Cstar :=
    ⟨(y.toReal + Cstar) / 2, by linarith, by linarith⟩
  obtain ⟨N, hN⟩ := h b hbC
  have hyb' : y < ENNReal.ofReal b := by
    rw [← ENNReal.ofReal_toReal hyfin]
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith [ENNReal.toReal_nonneg (a := y)])).mpr hyb
  filter_upwards [eventually_atTop.2 ⟨max N 1, fun n hn => hn⟩] with n hn
  have hn1 : 1 ≤ n := le_trans (le_max_right N 1) hn
  have hNn : N ≤ n := le_trans (le_max_left N 1) hn
  have hsn : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn1)
  have hs0 : ENNReal.ofReal (Real.sqrt n) ≠ 0 := (ENNReal.ofReal_pos.mpr hsn).ne'
  have hst : ENNReal.ofReal (Real.sqrt n) ≠ ∞ := ENNReal.ofReal_ne_top
  rw [ENNReal.lt_div_iff_mul_lt (Or.inl hs0) (Or.inl hst)]
  calc y * ENNReal.ofReal (Real.sqrt n)
      < ENNReal.ofReal b * ENNReal.ofReal (Real.sqrt n) := by gcongr
    _ ≤ weakConstant n := hN n hNn

/-- The manuscript's conclusion for all sufficiently large integer dimensions:
`C_n ≥ √n/35`, as an `ℝ≥0∞` inequality. -/
theorem sqrt_div_35_eventually
    (h : ∀ b : ℝ, b < Cstar → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ENNReal.ofReal b * ENNReal.ofReal (Real.sqrt n) ≤ weakConstant n) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ENNReal.ofReal (Real.sqrt n / 35) ≤ weakConstant n := by
  obtain ⟨N, hN⟩ := h (1 / 35) Cstar_gt_one_div_35
  refine ⟨N, fun n hn => ?_⟩
  have h35 : Real.sqrt n / 35 = (1 / 35 : ℝ) * Real.sqrt n := by ring
  rw [h35, ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 1/35)]
  exact hN n hn

/-- The converse passage: the `liminf` statement itself implies the manuscript's
"`C_n ≥ √n/35` for every sufficiently large integer `n`" corollary.  Together with
`liminf_sqrt_ge` this closes the logical circle between the two formulations the
manuscript uses. -/
theorem sqrt_div_35_of_liminf
    (hlim : ENNReal.ofReal Cstar ≤
      Filter.liminf (fun n : ℕ => weakConstant n / ENNReal.ofReal (Real.sqrt n))
        Filter.atTop) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ENNReal.ofReal (Real.sqrt n / 35) ≤ weakConstant n := by
  have h35 : ENNReal.ofReal (1 / 35 : ℝ) < ENNReal.ofReal Cstar :=
    (ENNReal.ofReal_lt_ofReal_iff Cstar_pos).mpr Cstar_gt_one_div_35
  have key := hlim
  rw [le_liminf_iff] at key
  have hev : ∀ᶠ n : ℕ in Filter.atTop,
      ENNReal.ofReal (1 / 35 : ℝ) < weakConstant n / ENNReal.ofReal (Real.sqrt n) :=
    key _ h35
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
  refine ⟨max N 1, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_right N 1) hn
  have hNn : N ≤ n := le_trans (le_max_left N 1) hn
  have hsn : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn1)
  have hs0 : ENNReal.ofReal (Real.sqrt n) ≠ 0 := (ENNReal.ofReal_pos.mpr hsn).ne'
  have hst : ENNReal.ofReal (Real.sqrt n) ≠ ∞ := ENNReal.ofReal_ne_top
  have hmul : ENNReal.ofReal (1 / 35 : ℝ) * ENNReal.ofReal (Real.sqrt n) ≤ weakConstant n :=
    (ENNReal.le_div_iff_mul_le (Or.inl hs0) (Or.inl hst)).mp (le_of_lt (hN n hNn))
  rwa [← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 1 / 35),
    show (1 / 35 : ℝ) * Real.sqrt n = Real.sqrt n / 35 by ring] at hmul

/-- The same conclusion for the real constant `C_n`, under the (mathematically
automatic, here explicit) finiteness hypothesis needed to read `ℝ≥0∞` as `ℝ`. -/
theorem sqrt_div_35_eventually_toReal
    (hfin : ∀ n : ℕ, weakConstant n ≠ ∞)
    (h : ∀ b : ℝ, b < Cstar → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ENNReal.ofReal b * ENNReal.ofReal (Real.sqrt n) ≤ weakConstant n) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Real.sqrt n / 35 ≤ (weakConstant n).toReal := by
  obtain ⟨N, hN⟩ := sqrt_div_35_eventually h
  refine ⟨N, fun n hn => ?_⟩
  exact (ofReal_le_weakConstant_iff (by positivity) (hfin n)).mp (hN n hn)

end CenteredCube

#print axioms CenteredCube.Cstar_pos
#print axioms CenteredCube.Cstar_gt_one_div_35
#print axioms CenteredCube.liminf_sqrt_ge
#print axioms CenteredCube.sqrt_div_35_eventually
#print axioms CenteredCube.sqrt_div_35_of_liminf
#print axioms CenteredCube.sqrt_div_35_eventually_toReal
