import TrueTiltMean
import Mathlib.Analysis.Calculus.Deriv.MeanValue

open Set

namespace CubeSqrtProbability

noncomputable def logResidual (x : ℝ) : ℝ := Real.log (1+x)-x

private theorem logResidual_slope_le_of_lt {a x y : ℝ} (ha : a ≤ 1/2) (hxy : x < y)
    (hx : |x| ≤ a) (hy : |y| ≤ a) :
    |logResidual y-logResidual x| ≤ 2*a*|y-x| := by
  have hz (z : ℝ) (hz : z ∈ Icc x y) : |z| ≤ a :=
    abs_le.mpr ⟨((abs_le.mp hx).1).trans hz.1,hz.2.trans (abs_le.mp hy).2⟩
  have hDeriv (z : ℝ) (hz' : z ∈ Icc x y) :
      HasDerivAt logResidual ((1+z)⁻¹-1) z := by
    have hp : 0 < 1+z := by linarith [(abs_le.mp (hz z hz')).1]
    change HasDerivAt ((fun y : ℝ ↦ Real.log (1+y)) - id) ((1+z)⁻¹-1) z
    simpa only [id_eq, one_div] using
      (((hasDerivAt_id z).const_add 1).log hp.ne').sub (hasDerivAt_id z)
  have hc : ContinuousOn logResidual (Icc x y) :=
    fun z hz' ↦ (hDeriv z hz').continuousAt.continuousWithinAt
  obtain ⟨z,hz',he⟩ := exists_hasDerivAt_eq_slope logResidual
    (fun z ↦ (1+z)⁻¹-1) hxy hc (fun t ht ↦ hDeriv t ⟨ht.1.le,ht.2.le⟩)
  have hzA := hz z ⟨hz'.1.le,hz'.2.le⟩
  have hp : 0 < 1+z := by linarith [(abs_le.mp hzA).1]
  have hD : |(1+z)⁻¹-1| ≤ 2*a := by
    have e : (1+z)⁻¹-1 = -z/(1+z) := by field_simp; ring
    rw [e,abs_div,abs_neg,abs_of_pos hp,div_le_iff₀ hp]
    have ha0 := (abs_nonneg z).trans hzA
    nlinarith [mul_nonneg ha0 (show 0 ≤ 1+2*z by linarith [(abs_le.mp hzA).1])]
  have he' : logResidual y-logResidual x = ((1+z)⁻¹-1)*(y-x) :=
    ((eq_div_iff (sub_ne_zero.mpr hxy.ne')).mp he).symm
  rw [he',abs_mul]
  exact mul_le_mul_of_nonneg_right hD (abs_nonneg _)

theorem true_log_increment_error {a x y : ℝ} (ha : a ≤ 1/2)
    (hx : |x| ≤ a) (hy : |y| ≤ a) :
    |(Real.log (1+y)-Real.log (1+x))-(y-x)| ≤ 2*a*|y-x| := by
  have e : (Real.log (1+y)-Real.log (1+x))-(y-x) = logResidual y-logResidual x := by
    unfold logResidual
    ring
  rw [e]
  rcases lt_trichotomy x y with hh | rfl | hh
  · exact logResidual_slope_le_of_lt ha hh hx hy
  · simp
  · rw [abs_sub_comm (logResidual y) (logResidual x),abs_sub_comm y x]
    exact logResidual_slope_le_of_lt ha hh hy hx

theorem true_log_increment_bound {a x y : ℝ} (ha : a ≤ 1/2)
    (hx : |x| ≤ a) (hy : |y| ≤ a) :
    |Real.log (1+y)-Real.log (1+x)| ≤ 2*|y-x| := by
  have he := true_log_increment_error ha hx hy
  let D := Real.log (1+y)-Real.log (1+x)
  calc
    |D| = |(D-(y-x))+(y-x)| := by rw [sub_add_cancel]
    _ ≤ |D-(y-x)| + |y-x| := abs_add_le _ _
    _ ≤ 2*a*|y-x| + |y-x| := add_le_add he (le_refl _)
    _ ≤ _ := by nlinarith [mul_nonneg (show 0 ≤ 1-2*a by linarith) (abs_nonneg (y-x))]

end CubeSqrtProbability
#print axioms CubeSqrtProbability.true_log_increment_error
#print axioms CubeSqrtProbability.true_log_increment_bound
