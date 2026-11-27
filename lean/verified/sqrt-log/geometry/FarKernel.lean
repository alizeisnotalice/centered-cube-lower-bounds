import Continuous
import ClosedForm
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

namespace CenteredCube.RudinDensity

theorem norm_DK_far {K : ℕ} (hK : 1 ≤ K) {τ : ℝ}
    (hτ : 0 < |τ|) (hHi : |τ| ≤ (K:ℝ)/8) :
    ‖DK K τ‖ ≤ 1 / (2 * |τ|) := by
  have hK' : (0:ℝ) < (K:ℝ) := by exact_mod_cast (show 0 < K by omega)
  have ha : |Real.pi * τ / (K:ℝ)| = Real.pi * |τ| / (K:ℝ) := by
    rw [abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos hK']
  have h₀ : |Real.pi * τ / (K:ℝ)| ≤ Real.pi / 2 := by
    rw [ha]
    apply (div_le_iff₀ hK').2
    have hh := mul_le_mul_of_nonneg_left hHi Real.pi_pos.le
    have hh' : 0 ≤ Real.pi * (K:ℝ) := by positivity
    nlinarith only [hh, hh']
  have jordan := Real.mul_abs_le_abs_sin h₀
  rw [ha] at jordan
  have hprod : 2 * |τ| ≤ (K:ℝ) * |Real.sin (Real.pi * τ / (K:ℝ))| := by
    have he : (K:ℝ) * (2 / Real.pi * (Real.pi * |τ| / (K:ℝ))) = 2 * |τ| := by
      field_simp
    rw [← he]
    exact mul_le_mul_of_nonneg_left jordan hK'.le
  have h2 : 0 < 2 * |τ| := by positivity
  have hsine : Real.sin (Real.pi * τ / (K:ℝ)) ≠ 0 := by
    intro h
    simp [h] at hprod
    linarith
  rw [norm_DK_eq hK hsine]
  calc
    _ ≤ 1 / ((K:ℝ) * |Real.sin (Real.pi * τ / (K:ℝ))|) :=
      div_le_div_of_nonneg_right (Real.abs_sin_le_one _) (h2.le.trans hprod)
    _ ≤ _ := one_div_le_one_div_of_le h2 hprod

theorem covariance_far {K : ℕ} (hK : 4 ≤ K) {u t s : ℝ}
    (hu : 3/50 ≤ u)
    (ht : |t - (K:ℝ)/4| ≤ (K:ℝ)/(100*u))
    (hs : |s - (K:ℝ)/4| ≤ (K:ℝ)/(100*u))
    (hlo : 0 < |t-s|) (hhi : |t-s| ≤ (K:ℝ)/8) :
    |kappa K t s| ≤ 1 / (2 * |t-s|) + 8 / (K:ℝ) := by
  have hn := norm_DK_far (K := K) (by omega) hlo hhi
  have hre : |ReDK K (t-s)| ≤ 1 / (2*|t-s|) :=
    (Complex.abs_re_le_norm _).trans hn
  have he := finite_kernel hK hu ht hs
  calc
    |kappa K t s| = |(kappa K t s - ReDK K (t-s)) + ReDK K (t-s)| := by
      rw [sub_add_cancel]
    _ ≤ |kappa K t s - ReDK K (t-s)| + |ReDK K (t-s)| := abs_add_le _ _
    _ ≤ _ := by linarith

end CenteredCube.RudinDensity

#print axioms CenteredCube.RudinDensity.norm_DK_far
#print axioms CenteredCube.RudinDensity.covariance_far
