import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

namespace CenteredCube.RudinDensity
open Finset

/-- Positive integer Gaussian tail, bounded by the geometric tail in
Region I of the manuscript. -/
theorem sum_gaussian_lags_le (s : Finset ℕ) (hs : ∀ m ∈ s, 1 ≤ m)
    {a : ℝ} (ha : 0 < a) :
    ∑ m ∈ s, Real.exp (-(a ^ 2 * (m : ℝ) ^ 2)) ≤
      1 / (Real.exp (a ^ 2) - 1) := by
  let r := Real.exp (-(a ^ 2))
  have hr : 0 < r := Real.exp_pos _
  have hrl : r < 1 := by
    dsimp [r]
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by nlinarith)
  calc
    (∑ m ∈ s, Real.exp (-(a ^ 2 * (m : ℝ) ^ 2))) ≤
        ∑ m ∈ s, r ^ m := by
      refine Finset.sum_le_sum fun m hm => ?_
      have hlow : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hs m hm
      have hsq : (m : ℝ) ≤ (m : ℝ)^2 := by
        simpa [mul_sub, sq] using mul_nonneg (show 0 ≤ (m : ℝ) by positivity)
          (sub_nonneg.mpr hlow)
      dsimp [r]
      rw [← Real.exp_nat_mul]
      apply Real.exp_le_exp.mpr
      have h' := mul_le_mul_of_nonneg_left hsq (sq_nonneg a)
      nlinarith only [h']
    _ ≤ r * (1 / (1 - r)) := by
      have hinj : Set.InjOn (fun m : ℕ => m - 1) ↑s := by
        intro m hm n hn hmn
        have h₁ := hs m hm
        have h₂ := hs n hn
        change m - 1 = n - 1 at hmn
        omega
      have hsum := summable_geometric_of_lt_one hr.le hrl
      have hsume : (∑ i ∈ s.image (fun m : ℕ => m - 1), r ^ i) ≤
          1 / (1-r) := by
        simpa [one_div, tsum_geometric_of_lt_one hr.le hrl] using
          hsum.sum_le_tsum (s.image (fun m : ℕ => m - 1)) (fun i _ => pow_nonneg hr.le i)
      rw [Finset.sum_image hinj] at hsume
      calc
        (∑ m ∈ s, r ^ m) = r * (∑ m ∈ s, r ^ (m - 1)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun m hm => ?_
          rw [← pow_succ', show m - 1 + 1 = m by have := hs m hm; omega]
        _ ≤ _ := mul_le_mul_of_nonneg_left hsume hr.le
    _ = _ := by
      have hpos : 0 < Real.exp (a^2) := Real.exp_pos _
      have hgt : 1 < Real.exp (a^2) := by
        rw [← Real.exp_zero]
        exact Real.exp_lt_exp.mpr (by nlinarith)
      dsimp [r]
      rw [Real.exp_neg]
      have hd : 0 < Real.exp (a^2) - 1 := sub_pos.mpr hgt
      have hn : 1 - (Real.exp (a^2))⁻¹ ≠ 0 := sub_ne_zero.mpr
        (ne_of_gt (by exact (inv_lt_one₀ hpos).2 hgt))
      field_simp

end CenteredCube.RudinDensity

#print axioms CenteredCube.RudinDensity.sum_gaussian_lags_le
