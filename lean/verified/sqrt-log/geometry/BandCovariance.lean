import GlobalKernel
import QuadraticKernel
import FourRegions

namespace CenteredCube.RudinDensity

variable {K : ℕ} {t s u a : ℝ} {m : ℕ}

theorem band0_covariance (hK : 4 ≤ K) (hu : 3/50 ≤ u) (ha : 0 < a)
    (ht : |t-(K:ℝ)/4| ≤ (K:ℝ)/(100*u))
    (hs : |s-(K:ℝ)/4| ≤ (K:ℝ)/(100*u))
    (hm : 1 ≤ m) (hτ : |t-s| = (m:ℝ)*a/u)
    (hscale : 2*u^2/a^2 ≤ (K:ℝ)) (hr : lagBand a u m = 0) :
    kappa K t s ≤ 1 - 4 * |t-s|^2 := by
  have hu' : 0 < u := by linarith
  have hm' : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  have hlo : a/u ≤ |t-s| := by
    rw [hτ]
    exact div_le_div_of_nonneg_right (by simpa using mul_le_mul_of_nonneg_right hm' ha.le) hu'.le
  have hhi : |t-s| ≤ 1/8 := by
    rw [hτ]
    unfold lagBand at hr
    split at hr
    · assumption
    split at hr
    · norm_num at hr
    split at hr <;> norm_num at hr
  linarith only [(covariance_quadratic hK hu ha ht hs hlo hhi hscale).1]

theorem band1_lag (hτ : |t-s| = (m:ℝ)*a/u) (hr : lagBand a u m = 1) :
    1/8 ≤ |t-s| := by
  rw [hτ]
  unfold lagBand at hr
  split at hr
  · norm_num at hr
  · linarith [lt_of_not_ge (by assumption :
      ¬ (m:ℝ)*a/u ≤ 1/8)]

theorem band2_lag (hτ : |t-s| = (m:ℝ)*a/u) (hr : lagBand a u m = 2) :
    32 ≤ |t-s| := by
  rw [hτ]
  unfold lagBand at hr
  split at hr
  · norm_num at hr
  split at hr
  · norm_num at hr
  · linarith [lt_of_not_ge (by assumption :
      ¬ (m:ℝ)*a/u ≤ 32)]

theorem band3_lag (hτ : |t-s| = (m:ℝ)*a/u) (hr : lagBand a u m = 3) :
    u^3 ≤ |t-s| := by
  rw [hτ]
  unfold lagBand at hr
  split at hr
  · norm_num at hr
  split at hr
  · norm_num at hr
  split at hr
  · norm_num at hr
  · linarith [lt_of_not_ge (by assumption :
      ¬ (m:ℝ)*a/u ≤ u^3)]

theorem covariance_band2 {K : ℕ} {t s : ℝ} (hK : 64 ≤ K) (hτ : 32 ≤ |t-s|)
    (hbound : |kappa K t s| ≤ 1/(2*|t-s|) + 8/(K:ℝ)) :
    kappa K t s ≤ 1/2 := by
  have hkR : (64:ℝ) ≤ (K:ℝ) := by exact_mod_cast hK
  have hf : 1/(2*|t-s|) ≤ 1/(64:ℝ) :=
    one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hb : 8/(K:ℝ) ≤ 8/(64:ℝ) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hkR
  linarith only [hf,hb,hbound,le_abs_self (kappa K t s)]

theorem covariance_band3 {K : ℕ} {t s u : ℝ} (hK : 0 < K) (hu : 0 < u)
    (hτ : u^3 ≤ |t-s|) (hbound : |kappa K t s| ≤ 1/(2*|t-s|) + 8/(K:ℝ)) :
    kappa K t s ≤ 8*(1/u^3+1/(K:ℝ)) := by
  have hL : 1/(2*|t-s|) ≤ 1/u^3 :=
    one_div_le_one_div_of_le (by positivity) (by linarith only [hτ, abs_nonneg (t-s)])
  have hP : 0 ≤ 1/u^3 := by positivity
  have he : 8*(1/u^3+1/(K:ℝ)) = 8*(1/u^3) + 8/(K:ℝ) := by ring
  rw [he]
  linarith only [hL,hbound,hP,le_abs_self (kappa K t s)]

end CenteredCube.RudinDensity

#print axioms CenteredCube.RudinDensity.band0_covariance
#print axioms CenteredCube.RudinDensity.covariance_band2
#print axioms CenteredCube.RudinDensity.covariance_band3
