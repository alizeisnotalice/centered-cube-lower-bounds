import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Tactic

open Set
open scoped Interval

namespace CubeSqrtProbability

/-- Exact third-order Lagrange estimate for a degree-two Taylor expansion along
the unit interval, retaining the factor 1/6. -/
theorem unit_segment_taylor_second_error (f : ℝ → ℝ) (hf : ContDiff ℝ 3 f)
    (C : ℝ) (hc : ∀ y ∈ Ioo (0:ℝ) 1, |iteratedDeriv 3 f y| ≤ C) :
    |f 1 - (f 0 + iteratedDeriv 1 f 0 + iteratedDeriv 2 f 0 / 2)| ≤ C/6 := by
  have hd : UniqueDiffOn ℝ (Icc (0:ℝ) 1) := uniqueDiffOn_Icc (by norm_num)
  have hi : (0:ℝ) ∈ Icc (0:ℝ) 1 := by norm_num
  have hd₁ : ContDiffAt ℝ 1 f 0 := hf.contDiffAt.of_le (by norm_num)
  have hd₂ : ContDiffAt ℝ 2 f 0 := hf.contDiffAt.of_le (by norm_num)
  have h1 := iteratedDerivWithin_eq_iteratedDeriv hd hd₁ hi
  have h2 := iteratedDerivWithin_eq_iteratedDeriv hd hd₂ hi
  have hTaylor : taylorWithinEval f 2 (Icc (0:ℝ) 1) 0 1 =
      f 0 + iteratedDeriv 1 f 0 + iteratedDeriv 2 f 0/2 := by
    let S := Icc (0:ℝ) 1
    have hTwo : taylorWithinEval f 2 S 0 1 =
        taylorWithinEval f 1 S 0 1 + (2:ℝ)⁻¹ * iteratedDerivWithin 2 f S 0 := by
      simpa only [Nat.factorial_one, Nat.cast_one, show (1:ℝ)+1=2 by norm_num,
        show (1:ℕ)+1=2 by decide, mul_one, sub_zero,
        one_pow, smul_eq_mul] using taylorWithinEval_succ f 1 S 0 1
    have hOne : taylorWithinEval f 1 S 0 1 =
        taylorWithinEval f 0 S 0 1 + iteratedDerivWithin 1 f S 0 := by
      simpa only [Nat.factorial_zero, Nat.cast_zero, Nat.cast_one, zero_add, mul_one,
        inv_one, sub_zero, one_pow, one_mul, smul_eq_mul] using
          taylorWithinEval_succ f 0 S 0 1
    change taylorWithinEval f 2 S 0 1 = _
    rw [hTwo,hOne,taylor_within_zero_eval]
    dsimp only [S]
    rw [h1,h2]
    ring
  obtain ⟨z,hz,he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (f := f) (x₀ := 0) (x := 1) (n := 2) (by norm_num) hf.contDiffOn
  rw [uIoo_of_le zero_le_one] at hz
  rw [uIcc_of_le zero_le_one,hTaylor] at he
  norm_num at he
  rw [iteratedDeriv_one,he,abs_div,abs_of_pos (by norm_num : (0:ℝ)<6)]
  exact div_le_div_of_nonneg_right (hc z hz) (by norm_num)

end CubeSqrtProbability
#print axioms CubeSqrtProbability.unit_segment_taylor_second_error
