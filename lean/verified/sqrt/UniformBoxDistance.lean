import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

open Set MeasureTheory
open scoped Interval

namespace CubeSqrtEnd

theorem integral_abs_sub_on_interval {a b x : ℝ} (hax : a ≤ x) (hxb : x ≤ b) :
    (∫ y in a..b, |x - y|) = (x-a)^2/2 + (b-x)^2/2 := by
  have fcont : Continuous (fun y : ℝ => |x - y|) := (continuous_const.sub continuous_id).abs
  rw [← intervalIntegral.integral_add_adjacent_intervals
      (fcont.intervalIntegrable _ _) (fcont.intervalIntegrable _ _)]
  have hleft :
      (∫ y in a..x, |x-y|) = (∫ y in a..x, x-y) := by
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le hax]
    intro y hy
    exact abs_of_nonneg (sub_nonneg.2 hy.2)
  have hright :
      (∫ y in x..b, |x-y|) = (∫ y in x..b, y-x) := by
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le hxb]
    intro y hy
    change |x-y| = y-x
    rw [abs_of_nonpos (sub_nonpos.2 hy.1)]
    ring
  rw [hleft, hright,
    intervalIntegral.integral_sub
      (show IntervalIntegrable (fun _ : ℝ => x) volume a x from continuous_const.intervalIntegrable _ _)
      (show IntervalIntegrable (fun y : ℝ => y) volume a x from continuous_id.intervalIntegrable _ _),
    intervalIntegral.integral_sub
      (show IntervalIntegrable (fun y : ℝ => y) volume x b from continuous_id.intervalIntegrable _ _)
      (show IntervalIntegrable (fun _ : ℝ => x) volume x b from continuous_const.intervalIntegrable _ _)]
  simp only [intervalIntegral.integral_const, smul_eq_mul, integral_id]
  ring

theorem integral_double_abs_sub_interval {a b : ℝ} (hab : a ≤ b) :
    (∫ x in a..b, ∫ y in a..b, |x-y|) = (b-a)^3 / 3 := by
  have hp :
      (∫ x in a..b, ∫ y in a..b, |x-y|) =
      (∫ x in a..b, x^2 - (a+b)*x + (a^2+b^2)/2) := by
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le hab]
    intro x hx
    change (∫ y in a..b, |x-y|) = x^2 - (a+b)*x + (a^2+b^2)/2
    rw [integral_abs_sub_on_interval hx.1 hx.2]
    ring
  rw [hp]
  have hc : Continuous (fun x : ℝ => x^2-(a+b)*x) :=
    (continuous_id.pow 2).sub (continuous_const.mul continuous_id)
  rw [intervalIntegral.integral_add (hc.intervalIntegrable _ _)
    (continuous_const.intervalIntegrable _ _),
    intervalIntegral.integral_sub
      (show IntervalIntegrable (fun x : ℝ => x^2) volume a b from
        (continuous_id.pow 2).intervalIntegrable _ _)
      (show IntervalIntegrable (fun x : ℝ => (a+b)*x) volume a b from
        (continuous_const.mul continuous_id).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul]
  simp only [intervalIntegral.integral_const, smul_eq_mul, integral_id, integral_pow]
  norm_num
  ring

/-- Expected distance of two independent lengths uniformly sampled in the
same interval. The division by length squared normalizes the box measure. -/
theorem uniform_box_expected_distance {a b : ℝ} (hab : a < b) :
    (∫ x in Icc a b, ∫ y in Icc a b, |x-y|) / (b-a)^2 = (b-a)/3 := by
  simp_rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab.le]
  rw [integral_double_abs_sub_interval hab.le]
  field_simp [sub_ne_zero.mpr hab.ne.symm]

theorem uniform_centered_box_expected_distance {δ : ℝ} (hδ : 0 < δ) :
    (∫ x in Icc (-(δ/2)) (δ/2), ∫ y in Icc (-(δ/2)) (δ/2), |x-y|) / δ^2 = δ/3 := by
  have hs : δ/2 - (-(δ/2)) = δ := by ring
  have h := uniform_box_expected_distance (a := -(δ/2)) (b := δ/2) (by linarith)
  rwa [hs] at h

#print axioms integral_abs_sub_on_interval
#print axioms integral_double_abs_sub_interval
#print axioms uniform_box_expected_distance
#print axioms uniform_centered_box_expected_distance
end CubeSqrtEnd
