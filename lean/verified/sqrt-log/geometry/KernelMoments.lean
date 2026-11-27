import Kernel

open MeasureTheory intervalIntegral

namespace CenteredCube.RudinDensity

noncomputable def normalizedScore (K : ℕ) (t x : ℝ) : ℝ :=
  Sfun K t x / Real.sqrt (VK K t)

theorem normalizedScore_cont (K : ℕ) (t : ℝ) : Continuous (normalizedScore K t) := by
  unfold normalizedScore Sfun
  fun_prop

theorem normalizedScore_mean (K : ℕ) (hK : 1 ≤ K) (t : ℝ) :
    ∫ x in (0:ℝ)..1, normalizedScore K t x = 0 := by
  unfold normalizedScore
  rw [intervalIntegral.integral_div, integral_Sfun K hK t, zero_div]

theorem normalizedScore_sq (K : ℕ) (hK : 1 ≤ K) (t : ℝ) (hV : 0 < VK K t) :
    ∫ x in (0:ℝ)..1, normalizedScore K t x ^ 2 = 1 := by
  unfold normalizedScore
  rw [integral_scaled_sq K hK t (Real.sqrt_pos.2 hV).ne', Real.sq_sqrt hV.le]
  change VK K t / VK K t = 1
  exact div_self hV.ne'

theorem normalizedScore_covariance (K : ℕ) (t s : ℝ) (hVt : 0 < VK K t)
    (hVs : 0 < VK K s) :
    ∫ x in (0:ℝ)..1, normalizedScore K t x * normalizedScore K s x = kappa K t s := by
  unfold normalizedScore kappa
  rw [← intervalIntegral.integral_div, Real.sqrt_mul hVt.le]
  apply intervalIntegral.integral_congr
  intro x _
  simp only [div_mul_div_comm]

theorem normalizedScore_abs_le {K : ℕ} (hK : 4 ≤ K) {u t : ℝ}
    (hu : 3/50 ≤ u)
    (ht : |t - (K:ℝ)/4| ≤ (K:ℝ)/(100*u)) (x : ℝ) :
    |normalizedScore K t x| ≤ 5 * Real.sqrt 8 := by
  unfold normalizedScore
  simpa only [abs_div, abs_of_nonneg (Real.sqrt_nonneg _)] using
    (abs_Y_le_window (x := x) hK hu ht)

noncomputable def sumScore (K : ℕ) (t s x : ℝ) : ℝ :=
  (normalizedScore K t x + normalizedScore K s x) /
    Real.sqrt (2*(1 + kappa K t s))

theorem sumScore_mean (K : ℕ) (hK : 1 ≤ K) (t s : ℝ) :
    ∫ x in (0:ℝ)..1, sumScore K t s x = 0 := by
  unfold sumScore
  have h1 : IntervalIntegrable (normalizedScore K t) volume 0 1 :=
    (normalizedScore_cont K t).intervalIntegrable 0 1
  have h2 : IntervalIntegrable (normalizedScore K s) volume 0 1 :=
    (normalizedScore_cont K s).intervalIntegrable 0 1
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add h1 h2,
    normalizedScore_mean K hK t, normalizedScore_mean K hK s, add_zero, zero_div]

theorem sumScore_sq (K : ℕ) (hK : 1 ≤ K) (t s : ℝ)
    (hVt : 0 < VK K t) (hVs : 0 < VK K s) (hκ : 0 < 1 + kappa K t s) :
    ∫ x in (0:ℝ)..1, sumScore K t s x ^ 2 = 1 := by
  have h1 : IntervalIntegrable (fun x => normalizedScore K t x ^ 2) volume 0 1 :=
    ((normalizedScore_cont K t).pow 2).intervalIntegrable 0 1
  have h2 : IntervalIntegrable (fun x => normalizedScore K s x ^ 2) volume 0 1 :=
    ((normalizedScore_cont K s).pow 2).intervalIntegrable 0 1
  have h12 : IntervalIntegrable (fun x => 2*(normalizedScore K t x*normalizedScore K s x)) volume 0 1 :=
    (((normalizedScore_cont K t).mul (normalizedScore_cont K s)).const_mul 2).intervalIntegrable 0 1
  have he : (fun x => sumScore K t s x ^ 2) = fun x =>
      (normalizedScore K t x ^ 2 + 2*(normalizedScore K t x*normalizedScore K s x) +
        normalizedScore K s x ^ 2) / Real.sqrt (2*(1 + kappa K t s))^2 := by
    funext x
    unfold sumScore
    rw [div_pow]
    congr 1
    ring
  rw [he, intervalIntegral.integral_div,
    intervalIntegral.integral_add
      (h1.add h12) h2,
    intervalIntegral.integral_add h1 h12, intervalIntegral.integral_const_mul,
    normalizedScore_sq K hK t hVt, normalizedScore_sq K hK s hVs,
    normalizedScore_covariance K t s hVt hVs, Real.sq_sqrt (by positivity)]
  have hc : 2*(1 + kappa K t s) ≠ 0 := by positivity
  apply (div_eq_iff hc).2
  ring

theorem covariance_le_one (K : ℕ) (hK : 1 ≤ K) (t s : ℝ)
    (hVt : 0 < VK K t) (hVs : 0 < VK K s) :
    kappa K t s ≤ 1 := by
  have h1 : IntervalIntegrable (fun x => normalizedScore K t x ^ 2) volume 0 1 :=
    ((normalizedScore_cont K t).pow 2).intervalIntegrable 0 1
  have h2 : IntervalIntegrable (fun x => normalizedScore K s x ^ 2) volume 0 1 :=
    ((normalizedScore_cont K s).pow 2).intervalIntegrable 0 1
  have h12 : IntervalIntegrable (fun x => 2*(normalizedScore K t x*normalizedScore K s x)) volume 0 1 :=
    (((normalizedScore_cont K t).mul (normalizedScore_cont K s)).const_mul 2).intervalIntegrable 0 1
  have h : 0 ≤ ∫ x in (0:ℝ)..1, (normalizedScore K t x - normalizedScore K s x)^2 :=
    intervalIntegral.integral_nonneg (by norm_num) (fun x _ => sq_nonneg _)
  have he : (fun x => (normalizedScore K t x - normalizedScore K s x)^2) =
      fun x => normalizedScore K t x^2 - 2*(normalizedScore K t x*normalizedScore K s x) +
        normalizedScore K s x^2 := by funext x; ring
  rw [he, intervalIntegral.integral_add (h1.sub h12) h2,
      intervalIntegral.integral_sub h1 h12, intervalIntegral.integral_const_mul,
      normalizedScore_sq K hK t hVt, normalizedScore_sq K hK s hVs,
      normalizedScore_covariance K t s hVt hVs] at h
  linarith

end CenteredCube.RudinDensity

#print axioms CenteredCube.RudinDensity.normalizedScore_mean
#print axioms CenteredCube.RudinDensity.normalizedScore_sq
#print axioms CenteredCube.RudinDensity.normalizedScore_covariance
#print axioms CenteredCube.RudinDensity.sumScore_mean
#print axioms CenteredCube.RudinDensity.sumScore_sq

#print axioms CenteredCube.RudinDensity.covariance_le_one
