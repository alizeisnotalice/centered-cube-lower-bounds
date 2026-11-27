import HeightComparison
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open Filter
open scoped Topology

namespace CenteredCube.RudinDensity

theorem lagDelta_pos : 0 < lagDelta := by
  have hm0 := globalMu_pos
  have hm1 : globalMu ≤ 1 := by
    unfold globalMu
    have hsin : 0 ≤ Real.sin (Real.pi/8) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by linarith [Real.pi_pos])
    exact sub_le_self _ (div_nonneg hsin (by positivity))
  unfold lagDelta
  apply sub_pos.mpr
  exact one_div_lt_one_div_of_lt (by linarith) (by linarith)

theorem exp_poly_quadratic_limit (k : ℕ) (d : ℝ) {b : ℝ} (hb : 0 < b) (hd : 0 ≤ d) :
    Tendsto (fun x : ℝ => (d*x^k+1)*Real.exp (-b*x^2)) atTop (𝓝 0) := by
  have h0 : Tendsto (fun x : ℝ => x^k * Real.exp (-b*x)) atTop (𝓝 0) := by
    simpa only [Real.rpow_natCast] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (k:ℝ) b hb)
  have h1 : Tendsto (fun x : ℝ => Real.exp (-b*x)) atTop (𝓝 0) := by
    simpa only [Real.rpow_zero, one_mul] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 b hb)
  have hu : Tendsto (fun x : ℝ => (d*x^k+1)*Real.exp (-b*x)) atTop (𝓝 0) := by
    have H := (h0.const_mul d).add h1
    convert H using 1
    · ext x
      ring
    · simp
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu ?_ ?_
  · filter_upwards [eventually_ge_atTop (0:ℝ)] with x hx
    positivity
  · filter_upwards [eventually_ge_atTop (1:ℝ)] with x hx
    have hnon : 0 ≤ (d*x^k+1) := by positivity
    have hsq : x ≤ x^2 := by nlinarith only [mul_nonneg (show 0 ≤ x by linarith) (sub_nonneg.mpr hx)]
    have hm := mul_le_mul_of_nonpos_left hsq (neg_nonpos.mpr hb.le)
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hm) hnon

theorem mid_ratio_zero {a : ℝ} (ha : 0 < a) :
    Tendsto (fun n => (32*paperU n/a+1)*Real.exp (-lagDelta*paperU n^2)) atTop (𝓝 0) := by
  have H := (exp_poly_quadratic_limit 1 (32/a) lagDelta_pos (by positivity)).comp paperU_tends_top
  apply H.congr'
  exact Eventually.of_forall (fun n => by dsimp; ring)

theorem outer_ratio_zero {a : ℝ} (ha : 0 < a) :
    Tendsto (fun n => (paperU n^3*paperU n/a+1)*Real.exp (-(1/6)*paperU n^2)) atTop (𝓝 0) := by
  have H := (exp_poly_quadratic_limit 4 (1/a) (b := 1/6) (by norm_num) (by positivity)).comp paperU_tends_top
  apply H.congr'
  exact Eventually.of_forall (fun n => by dsimp; ring)

theorem theta_u_sq_zero :
    Tendsto (fun n => lagTheta (paperK n) (paperU n)*paperU n^2) atTop (𝓝 0) := by
  have H₀ : Tendsto (fun n => (paperU n)⁻¹) atTop (𝓝 0) := paperU_tends_top.inv_tendsto_atTop
  have H : Tendsto (fun n => 8*((paperU n)⁻¹+paperU n^2/(paperK n:ℝ))) atTop (𝓝 0) := by
    simpa only [add_zero,mul_zero] using (H₀.add paperU_sq_over_K_zero).const_mul 8
  apply H.congr'
  filter_upwards [paperU_tends_top.eventually_ge_atTop 1,eventually_paperK_pos] with n hu hk
  have hu0 : paperU n ≠ 0 := by linarith
  have hk0 : (paperK n:ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  unfold lagTheta
  field_simp
  <;> ring

end CenteredCube.RudinDensity

#print axioms CenteredCube.RudinDensity.mid_ratio_zero
#print axioms CenteredCube.RudinDensity.outer_ratio_zero
#print axioms CenteredCube.RudinDensity.theta_u_sq_zero
