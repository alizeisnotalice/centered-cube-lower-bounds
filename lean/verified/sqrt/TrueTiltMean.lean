import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Tactic

open MeasureTheory
open scoped BigOperators

namespace CubeSqrtProbability

theorem log1p_quadratic_approx {a y : ℝ} (ha : a ≤ 1/2) (hy : |y| ≤ a) :
    |Real.log (1+y) - (y-y^2/2)| ≤ 2*a*y^2 := by
  have hsmall : |-y| < 1 := by rw [abs_neg]; linarith
  have hh := Real.abs_log_sub_add_sum_range_le hsmall 2
  rw [abs_neg] at hh
  norm_num [Finset.sum_range_succ] at hh
  have he : -y + y^2/2 + Real.log (1+y) = Real.log (1+y) - (y-y^2/2) := by ring
  have hh' : |Real.log (1+y) - (y-y^2/2)| ≤ |y|^3/(1-|y|) := by rw [← he]; exact hh
  refine hh'.trans ?_
  have hb : 0 < 1-|y| := by linarith
  have hn : 0 ≤ a := (abs_nonneg y).trans hy
  rw [div_le_iff₀ hb, pow_succ, sq_abs]
  calc
    y^2*|y| ≤ y^2*a := mul_le_mul_of_nonneg_left hy (sq_nonneg y)
    _ ≤ 2*a*y^2*(1-|y|) := by
      have hm : a ≤ 2*a*(1-|y|) := by nlinarith [mul_nonneg hn (show 0 ≤ 1-2*|y| by linarith)]
      calc
        _ = a*y^2 := by ring
        _ ≤ (2*a*(1-|y|))*y^2 := mul_le_mul_of_nonneg_right hm (sq_nonneg y)
        _ = _ := by ring

theorem single_tilt_log_mean_pointwise {a x y : ℝ} (ha : a ≤ 1/2)
    (hx : |x| ≤ a) (hy : |y| ≤ a) :
    |(1+x)*Real.log (1+y) - (y+x*y-y^2/2)| ≤ 4*a*y^2 := by
  let R := Real.log (1+y) - (y-y^2/2)
  have h1 : 0 < 1+x := by linarith [(abs_le.mp hx).1]
  have h2 : 1+x ≤ 3/2 := by linarith [(abs_le.mp hx).2]
  have hA : 0 ≤ a := (abs_nonneg x).trans hx
  have hR : |R| ≤ 2*a*y^2 := log1p_quadratic_approx ha hy
  have he : (1+x)*Real.log (1+y) - (y+x*y-y^2/2) = (1+x)*R-x*(y^2/2) := by
    unfold R
    ring
  rw [he]
  calc
    _ ≤ |(1+x)*R| + |x*(y^2/2)| := abs_sub _ _
    _ = (1+x)*|R| + |x| * (y^2/2) := by rw [abs_mul,abs_mul,abs_of_pos h1,abs_of_nonneg (by positivity : 0 ≤ y^2/2)]
    _ ≤ (3/2)*(2*a*y^2)+a*(y^2/2) :=
      add_le_add (mul_le_mul h2 hR (abs_nonneg _) (by norm_num))
        (mul_le_mul_of_nonneg_right hx (by positivity))
    _ ≤ _ := by nlinarith [mul_nonneg hA (sq_nonneg y)]

theorem exp_logPerturbation_eq {a x : ℝ} (ha : a ≤ 1/2) (hx : |x| ≤ a) :
    Real.exp (Real.log (1+x)) = 1+x := by
  apply Real.exp_log
  linarith [(abs_le.mp hx).1]

end CubeSqrtProbability
#print axioms CubeSqrtProbability.single_tilt_log_mean_pointwise
