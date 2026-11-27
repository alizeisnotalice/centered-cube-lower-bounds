import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Filter
open scoped Topology
namespace CubeSqrtOverlap

/-- c is the actual exponent coefficient (c_paper/8 for the shortcut,
c_paper/4 for the sharper manuscript pair summation). -/
noncomputable def retainedGap (c T : ℝ) : ℝ :=
  (8/c)*Real.log T

theorem retained_gap_exp_eq {c T : ℝ} (hc : 0 < c) (hT : 0 < T) :
    Real.exp (-c * retainedGap c T) = (T^8)⁻¹ := by
  have hE : -c*retainedGap c T = -((8:ℕ):ℝ)*Real.log T := by
    unfold retainedGap
    push_cast
    field_simp [hc.ne']
  rw [hE,neg_mul,Real.exp_neg, Real.exp_nat_mul,Real.exp_log hT]

theorem retained_gap_div_tendsto_zero (c : ℝ) :
    Tendsto (fun T : ℝ ↦ retainedGap c T/T) atTop (𝓝 0) := by
  have h := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have H := h.const_mul (8/c)
  simpa only [id_eq, mul_zero,retainedGap,mul_div_assoc] using H

theorem retained_gap_mesh_overlap_le {c T : ℝ} (hc : 0 < c) (hT : 1 ≤ T) :
    (T^3+1)^2 * Real.exp (-c*retainedGap c T)/(1-Real.exp (-c*(T+retainedGap c T))) ≤
      (4/(1-Real.exp (-c)))/T^2 := by
  have hT0 : 0 < T := zero_lt_one.trans_le hT
  have hD : 0 ≤ retainedGap c T := mul_nonneg (by positivity) (Real.log_nonneg hT)
  let A := 1-Real.exp (-c)
  let B := 1-Real.exp (-c*(T+retainedGap c T))
  have hA : 0 < A := by
    dsimp [A]
    exact sub_pos.mpr (Real.exp_lt_one_iff.2 (neg_neg_of_pos hc))
  have hAB : A ≤ B := by
    dsimp [A,B]
    apply sub_le_sub_left
    apply Real.exp_le_exp.mpr
    have h1 : 1 ≤ T+retainedGap c T := by linarith only [hT,hD]
    have h := mul_le_mul_of_nonneg_left h1 hc.le
    linarith only [h]
  have hTp : 1 ≤ T^3 := by simpa only [one_pow] using pow_le_pow_left₀ (show (0:ℝ)≤1 by norm_num) hT 3
  have hNum : (T^3+1)^2 ≤ (2*T^3)^2 := by
    apply pow_le_pow_left₀ (by positivity)
    linarith only [hTp]
  rw [retained_gap_exp_eq hc hT0]
  change ((T^3+1)^2)*(T^8)⁻¹/B ≤ (4/A)/T^2
  calc
    _ ≤ ((2*T^3)^2)*(T^8)⁻¹/B := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hNum (by positivity)) (hA.le.trans hAB)
    _ ≤ ((2*T^3)^2)*(T^8)⁻¹/A := div_le_div_of_nonneg_left (by positivity) hA hAB
    _ = _ := by field_simp [hT0.ne',hA.ne'] <;> ring

end CubeSqrtOverlap
#print axioms CubeSqrtOverlap.retained_gap_mesh_overlap_le
#print axioms CubeSqrtOverlap.retained_gap_div_tendsto_zero
