import SqrtGramNormalization

namespace CenteredCubeSqrt

theorem reference_kernel_near_gap {τ N D : ℝ}
    (hτ0 : 0≤τ) (hτ1 : τ≤1) (hD0 : 0<D) (hD : D≤121/87)
    (hC : 1+N≤D) :
    (87/121)*(1-(1-τ)^3)≤1-((1-τ)^3+N)/D := by
  have hr : 0≤1-τ := by linarith
  have hs : (1-τ)^3≤1 := by
    have h := pow_le_pow_left₀ hr (show 1-τ≤1 by linarith) 3
    norm_num at h
    exact h
  calc
    _ = (1-(1-τ)^3)/(121/87) := by ring
    _ ≤ (1-(1-τ)^3)/D := div_le_div_of_nonneg_left (by linarith) hD0 hD
    _ ≤ _ := by
      rw [show 1-((1-τ)^3+N)/D=(D-((1-τ)^3+N))/D by field_simp]
      apply div_le_div_of_nonneg_right _ hD0.le
      linarith

theorem normalized_kernel_small_gap {τ N D κ κ₀ ε : ℝ}
    (hτ : 0≤τ) (ht : τ≤1/8) (hD0 : 0<D) (hD : D≤121/87)
    (hC : 1+N≤D) (hκ₀ : κ₀=((1-τ)^3+N)/D) (hκ : |κ-κ₀|≤8*ε) :
    (174/121)*τ-8*ε≤1-κ := by
  have h := reference_kernel_near_gap hτ (by linarith : τ≤1) hD0 hD hC
  have hi : 2*τ≤1-(1-τ)^3 := by
    have h2 := mul_le_mul_of_nonneg_left ht hτ
    have h3 : 0≤τ^3 := by positivity
    nlinarith
  have h' := mul_le_mul_of_nonneg_left hi (show (0:ℝ)≤87/121 by norm_num)
  rw [←hκ₀] at h
  linarith [(abs_le.mp hκ).2]

theorem normalized_kernel_medium_gap {τ N D κ κ₀ ε : ℝ}
    (hτ : 1/8≤τ) (ht : τ≤1) (hD0 : 0<D) (hD : D≤121/87)
    (hC : 1+N≤D) (hκ₀ : κ₀=((1-τ)^3+N)/D) (hκ : |κ-κ₀|≤8*ε) :
    14703/61952-8*ε≤1-κ := by
  have h := reference_kernel_near_gap (by linarith : 0≤τ) ht hD0 hD hC
  have hp := pow_le_pow_left₀ (show 0≤1-τ by linarith) (show 1-τ≤7/8 by linarith) 3
  have hi : (169/512:ℝ)≤1-(1-τ)^3 := by norm_num at hp; linarith
  have h' := mul_le_mul_of_nonneg_left hi (show (0:ℝ)≤87/121 by norm_num)
  rw [←hκ₀] at h
  linarith [(abs_le.mp hκ).2]

#print axioms normalized_kernel_small_gap
#print axioms normalized_kernel_medium_gap

end CenteredCubeSqrt
