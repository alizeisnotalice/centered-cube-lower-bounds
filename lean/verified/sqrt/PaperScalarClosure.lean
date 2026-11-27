import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

open scoped Interval Topology
open Filter Set

namespace CubeSqrtEnd

noncomputable def paperConstant : ℝ := 87 / (220 * Real.sqrt (58 * Real.pi))

theorem paperConstant_pos : 0 < paperConstant := by
  unfold paperConstant
  exact div_pos (by norm_num) (mul_pos (by norm_num)
    (Real.sqrt_pos.2 (mul_pos (by norm_num) Real.pi_pos)))

theorem paperConstant_gt_rational : (1 : ℝ) / 35 < paperConstant := by
  have hpi : Real.pi < (22 : ℝ) / 7 := Real.pi_lt_d20.trans (by norm_num)
  have hs : Real.sqrt (58 * Real.pi) < (68 : ℝ) / 5 := by
    apply (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 68 / 5)).2
    linarith
  unfold paperConstant
  have hden : 0 < 220 * Real.sqrt (58 * Real.pi) :=
    mul_pos (by norm_num) (Real.sqrt_pos.2 (mul_pos (by norm_num) Real.pi_pos))
  apply (lt_div_iff₀ hden).2
  linarith

theorem paper_intensity_integral :
    (∫ L : ℝ in (10 / 9 : ℝ)..(11 / 9 : ℝ), (29 / 9 : ℝ) * L ^ (-2 : ℤ)) =
      29 / 110 := by
  have h0 : (0 : ℝ) ∉ [[(10 / 9 : ℝ), (11 / 9 : ℝ)]] := by
    rw [uIcc_of_le (by norm_num : (10 / 9 : ℝ) ≤ 11 / 9)]
    norm_num
  rw [intervalIntegral.integral_const_mul,
    integral_zpow (n := -2) (Or.inr ⟨by decide, h0⟩)]
  norm_num

theorem paper_constant_from_density (p : ℝ) :
    (3 * p / Real.sqrt 29) * (1 / Real.sqrt (2 * Real.pi)) / 2 *
       (∫ L : ℝ in (10 / 9 : ℝ)..(11 / 9 : ℝ), (29 / 9 : ℝ) * L ^ (-2 : ℤ)) =
      p * paperConstant := by
  rw [paper_intensity_integral]
  unfold paperConstant
  have h : Real.sqrt (58 * Real.pi) =
      Real.sqrt 29 * Real.sqrt (2 * Real.pi) := by
    rw [show (58 : ℝ) * Real.pi = 29 * (2 * Real.pi) by ring,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 29)]
  rw [h]
  have ha : Real.sqrt (29 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hb : Real.sqrt (2 * Real.pi) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (mul_pos (by norm_num) Real.pi_pos))
  field_simp [ha, hb]
  <;> ring

/-- Uniform positive backgrounds give all p<1. Close only the numeric bound,
never put p=1 in the density used for a witness. -/
theorem paper_bound_close_last_parameter {b : ℝ}
    (hb : ∀ p : ℝ, 0 < p → p < 1 → p * paperConstant ≤ b) :
    paperConstant ≤ b := by
  by_contra! h
  have hx : b / paperConstant < 1 := (div_lt_one paperConstant_pos).2 h
  let p := (max (b / paperConstant) 0 + 1) / 2
  have hp0 : 0 < p := by
    have := le_max_right (b / paperConstant) (0 : ℝ)
    dsimp [p]
    linarith
  have hm : max (b / paperConstant) 0 < 1 := max_lt hx (by norm_num)
  have hp1 : p < 1 := by dsimp [p]; linarith
  have hxp : b / paperConstant < p := by
    have := le_max_left (b / paperConstant) (0 : ℝ)
    dsimp [p]
    linarith
  exact (not_lt_of_ge (hb p hp0 hp1)) ((div_lt_iff₀ paperConstant_pos).1 hxp)

/-- If every finite retained packet gives a bound, the large packet limit
extracts the integrated intensity. No parameter is varied with the dimension. -/
theorem paper_packet_asymptotic_bound
    {b K k : ℝ} (A E D : ℕ → ℝ)
    (hA : Tendsto A atTop (𝓝 k))
    (hE : Tendsto E atTop (𝓝 0))
    (hD : Tendsto D atTop (𝓝 0))
    (hbound : ∀ᶠ T in atTop, K * ((A T - E T) / (1 + D T)) ≤ b) :
    K * k ≤ b := by
  have hden : Tendsto (fun T => 1 + D T) atTop (𝓝 (1 : ℝ)) := by
    simpa only [add_zero] using tendsto_const_nhds.add hD
  have hnum : Tendsto (fun T => A T - E T) atTop (𝓝 k) := by
    simpa only [sub_zero] using hA.sub hE
  have hquo : Tendsto (fun T => (A T - E T) / (1 + D T)) atTop (𝓝 k) := by
    simpa only [Pi.div_def, div_one] using hnum.div hden (one_ne_zero : (1 : ℝ) ≠ 0)
  exact le_of_tendsto (tendsto_const_nhds.mul hquo) hbound

#print axioms paper_packet_asymptotic_bound

#print axioms paperConstant_gt_rational
#print axioms paper_intensity_integral
#print axioms paper_constant_from_density
#print axioms paper_bound_close_last_parameter

end CubeSqrtEnd
