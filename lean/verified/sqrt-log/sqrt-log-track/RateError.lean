import Mathlib
namespace CubeMD
theorem tail_bound_of_rate_error
    (c C a L r δ p : ℝ) (hc : 0 ≤ c) (hC : 0 ≤ C) (ha : 0 < a)
    (herr : |L - r| ≤ δ)
    (hlo : c / a * Real.exp (-L) ≤ p)
    (hhi : p ≤ C / a * Real.exp (-L)) :
    c / a * Real.exp (-r - δ) ≤ p ∧ p ≤ C / a * Real.exp (-r + δ) := by
  rcases abs_le.mp herr with ⟨hl, hu⟩
  constructor
  · exact (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith))
      (div_nonneg hc ha.le)).trans hlo
  · exact hhi.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith))
      (div_nonneg hC ha.le))

theorem interval_error_of_cdf_errors
    (Fa Fb Ga Gb δ : ℝ) (ha : |Fa - Ga| ≤ δ) (hb : |Fb - Gb| ≤ δ) :
    |(Fb - Fa) - (Gb - Ga)| ≤ 2 * δ := by
  rw [show (Fb - Fa) - (Gb - Ga) = (Fb - Gb) - (Fa - Ga) by ring]
  calc
    |(Fb - Gb) - (Fa - Ga)| ≤ |Fb - Gb| + |Fa - Ga| := by
      simpa only [Real.norm_eq_abs] using norm_sub_le (Fb - Gb) (Fa - Ga)
    _ ≤ 2 * δ := by linarith
end CubeMD
#print axioms CubeMD.tail_bound_of_rate_error
#print axioms CubeMD.interval_error_of_cdf_errors
