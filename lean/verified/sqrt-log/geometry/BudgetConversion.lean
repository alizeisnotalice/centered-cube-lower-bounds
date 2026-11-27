import EventualBudgets

namespace CenteredCube.RudinDensity

noncomputable def rawMarginal (u : ℝ) : ℝ := marginalC/u*Real.exp (-(u^2/2))

theorem rawMarginal_nonneg {u : ℝ} (hu : 0 ≤ u) : 0 ≤ rawMarginal u := by
  unfold rawMarginal
  exact mul_nonneg (div_nonneg marginalC_pos.le hu) (Real.exp_pos _).le

theorem budget_convert_near {M a u : ℝ} (hM : 0 ≤ M) (hu : 0 < u)
    (h : singleUpper/(Real.exp (a^2)-1) ≤ marginalC/4) :
    M*(pairPrefactor u*Real.exp (-(u^2)/2))/(Real.exp (a^2)-1) ≤
      (M*rawMarginal u)/4 := by
  have H := mul_le_mul_of_nonneg_left h (show 0 ≤ M*Real.exp (-(u^2/2))/u by positivity)
  simp only [pairPrefactor,rawMarginal,singleUpper] at H ⊢
  conv_lhs => rw [show -(u^2)/2 = -(u^2/2) by ring]
  convert H using 1 <;> ring

theorem budget_convert_mid {M a u δ : ℝ} (hM : 0 ≤ M) (hu : 0 < u)
    (h : singleUpper*((32*u/a+1)*Real.exp (-δ*u^2)) ≤ marginalC/12) :
    M*(32*u/a+1)*(pairPrefactor u*(Real.exp (-(u^2)/2)*Real.exp (-δ*u^2))) ≤
      (M*rawMarginal u)/12 := by
  have H := mul_le_mul_of_nonneg_left h (show 0 ≤ M*Real.exp (-(u^2/2))/u by positivity)
  simp only [pairPrefactor,rawMarginal,singleUpper] at H ⊢
  conv_lhs => rw [show -(u^2)/2 = -(u^2/2) by ring]
  convert H using 1 <;> ring

theorem budget_convert_outer {M a u : ℝ} (hM : 0 ≤ M) (hu : 0 < u)
    (h : singleUpper*((u^3*u/a+1)*Real.exp (-(1/6)*u^2)) ≤ marginalC/12) :
    M*(u^3*u/a+1)*(pairPrefactor u*(Real.exp (-(u^2)/2)*Real.exp (-(1/6)*u^2))) ≤
      (M*rawMarginal u)/12 := by
  have H := mul_le_mul_of_nonneg_left h (show 0 ≤ M*Real.exp (-(u^2/2))/u by positivity)
  simp only [pairPrefactor,rawMarginal,singleUpper] at H ⊢
  conv_lhs => rw [show -(u^2)/2 = -(u^2/2) by ring]
  convert H using 1 <;> ring

theorem budget_convert_far {M u θ : ℝ} (hM : 0 ≤ M) (hu : 0 < u) (hθ : 0 ≤ θ)
    (h : singleUpper*(M*Real.exp (-(u^2/2))*Real.exp (θ*u^2/(1+θ))) ≤ marginalC/6) :
    (M^2/2)*(pairPrefactor u*Real.exp (-(u^2)/(1+θ))) ≤
      (M*rawMarginal u)/12 := by
  have H := mul_le_mul_of_nonneg_left h (show 0 ≤ M*Real.exp (-(u^2/2))/(2*u) by positivity)
  rw [far_ratio_identity hθ]
  simp only [pairPrefactor,rawMarginal,singleUpper] at H ⊢
  convert H using 1 <;> ring

end CenteredCube.RudinDensity

#print axioms CenteredCube.RudinDensity.budget_convert_near
#print axioms CenteredCube.RudinDensity.budget_convert_far
