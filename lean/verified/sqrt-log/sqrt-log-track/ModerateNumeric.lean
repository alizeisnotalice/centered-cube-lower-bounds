import RateError

namespace CubeMD

theorem md_lower_factor (L c z : ℝ) :
    Real.exp (-L-1) * (c/z) = (c/Real.exp 1)/z * Real.exp (-L) := by
  rw [Real.exp_sub]
  ring

theorem md_upper_factor (L C z R : ℝ) :
    Real.exp (-L) * (C/z) / R = (C/R)/z * Real.exp (-L) := by ring

theorem md_nonnegative_constants (c C : ℝ) (hc : 0 ≤ c) (hC : 0 ≤ C) :
    0 ≤ c/Real.exp 1 ∧ 0 ≤ C/(1-Real.exp (-1)) := by
  have hh : Real.exp (-1 : ℝ) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  exact ⟨div_nonneg hc (Real.exp_pos _).le, div_nonneg hC (sub_nonneg.mpr hh.le)⟩

theorem finish_md_numeric (p z L d c C : ℝ) (hz : 0 < z)
    (hc : 0 ≤ c) (hC : 0 ≤ C)
    (hRate : |L - z^2/2| ≤ d)
    (hL : Real.exp (-L-1) * (c/z) ≤ p)
    (hU : p ≤ Real.exp (-L)*(C/z)/(1-Real.exp (-1))) :
    (c/Real.exp 1)/z * Real.exp (-(z^2/2)-d) ≤ p ∧
      p ≤ (C/(1-Real.exp (-1)))/z * Real.exp (-(z^2/2)+d) := by
  have h := md_nonnegative_constants c C hc hC
  have hlo : (c / Real.exp 1) / z * Real.exp (-L) ≤ p :=
    (md_lower_factor L c z).symm.le.trans hL
  have hhi : p ≤ (C / (1 - Real.exp (-1))) / z * Real.exp (-L) :=
    hU.trans (md_upper_factor L C z (1 - Real.exp (-1))).le
  exact tail_bound_of_rate_error (c/Real.exp 1) (C/(1-Real.exp (-1))) z L (z^2/2) d p
    h.1 h.2 hz hRate hlo hhi

end CubeMD
#print axioms CubeMD.md_lower_factor
#print axioms CubeMD.md_upper_factor
#print axioms CubeMD.md_nonnegative_constants
#print axioms CubeMD.finish_md_numeric
