import ActualGrowth
import GlobalKernel

open Filter
namespace CenteredCube.RudinDensity

/-- All two-point moderate-deviation parameters are eventually valid, uniformly
over nonnegative u in the paper's unit-width window for its square. -/
theorem eventually_twopoint_conditions (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ u : ℝ, 1 ≤ u → |u^2-Real.log (n:ℝ)| ≤ 1 →
      readyMD n (pairB ε) ∧ (2*u/Real.sqrt (2*ε))^6 ≤ (n:ℝ) ∧
      72*(pairB ε)^3*(2*u/Real.sqrt (2*ε))^3/Real.sqrt (n:ℝ) ≤ 1 := by
  let W := 2/Real.sqrt (2*ε)
  let D := 72*(pairB ε)^3*W^3
  let A := max (W^6) (D^2)
  have hW : 0 < W := by dsimp only [W]; positivity
  have hA : 0 < A := (pow_pos hW _).trans_le (le_max_left _ _)
  filter_upwards [CubeMD.eventually_log_fourth_budget A hA,
    eventually_readyMD (pairB ε), eventually_gt_atTop (0:ℕ)] with n hBudget hMD hn
  intro u hu hround
  have hn' : 0 < (n:ℝ) := by exact_mod_cast hn
  have hN : 0 < Real.sqrt (n:ℝ) := Real.sqrt_pos.2 hn'
  have hu' : 0 < u := by linarith only [hu]
  have hu2 : 1 ≤ u^2 := by nlinarith [sq_nonneg (u-1)]
  have h68 : u^6 ≤ u^8 := by
    nlinarith only [mul_le_mul_of_nonneg_right hu2 (show 0 ≤ u^6 by positivity)]
  have h8 : u^8 ≤ (Real.log (n:ℝ)+1)^4 := by
    rw [show u^8 = (u^2)^4 by ring]
    exact pow_le_pow_left₀ (sq_nonneg _) (by linarith only [(abs_le.mp hround).2]) _
  have hPow := (mul_le_mul_of_nonneg_left (h68.trans h8) hA.le).trans hBudget
  have hw : 2*u/Real.sqrt (2*ε) = W*u := by dsimp only [W]; ring
  rw [hw]
  refine ⟨hMD, ?_, ?_⟩
  · calc
      _ = W^6*u^6 := mul_pow _ _ _
      _ ≤ A*u^6 := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ ≤ _ := hPow
  · apply (div_le_iff₀ hN).2
    rw [one_mul]
    apply le_of_sq_le_sq _ hN.le
    rw [Real.sq_sqrt hn'.le]
    calc
      _ = D^2*u^6 := by dsimp only [D]; ring
      _ ≤ A*u^6 := mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
      _ ≤ _ := hPow

theorem eventually_twopoint_conditions_globalNu :
    ∀ᶠ n : ℕ in atTop, ∀ u : ℝ, 1 ≤ u → |u^2-Real.log (n:ℝ)| ≤ 1 →
      readyMD n (pairB (globalNu/2)) ∧ (2*u/Real.sqrt (2*(globalNu/2)))^6 ≤ (n:ℝ) ∧
      72*(pairB (globalNu/2))^3*(2*u/Real.sqrt (2*(globalNu/2)))^3/Real.sqrt (n:ℝ) ≤ 1 :=
  eventually_twopoint_conditions (globalNu/2) (div_pos globalNu_pos (by norm_num))

end CenteredCube.RudinDensity
#print axioms CenteredCube.RudinDensity.eventually_twopoint_conditions
#print axioms CenteredCube.RudinDensity.eventually_twopoint_conditions_globalNu
