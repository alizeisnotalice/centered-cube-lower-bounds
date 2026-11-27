import FixedFaceRate
open Filter
open scoped Topology
namespace CubeSqrtProbability
set_option maxHeartbeats 1000000

/-- For v=O(log n), the fixed-face rate after choosing η=n^(-1/8)
is little o of 1/sqrt(v), as required by the weighted winning integral. -/
theorem fixed_face_weighted_rate_zero_along_dimensions (m : ℕ→ℕ) (hm : Tendsto m atTop atTop) (v : ℕ → ℝ) (A C S : ℝ)
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hS : 0 ≤ S)
    (hv : ∀ᶠ n in atTop, 0 ≤ v n ∧ v n ≤ A*Real.log (m n:ℝ)) :
    Tendsto (fun n : ℕ ↦
      Real.sqrt (v n) * ((m n:ℝ)^(-(1/8:ℝ)) * (C*(Real.sqrt (v n))^3 + S))) atTop (𝓝 0) := by
  have hLogRatio (p : ℝ) :
      Tendsto (fun n : ℕ ↦ (Real.log (m n:ℝ))^p / (m n:ℝ)^(1/8:ℝ)) atTop (𝓝 0) :=
    (isLittleO_log_rpow_rpow_atTop p (show (0:ℝ) < 1/8 by norm_num)).tendsto_div_nhds_zero.comp
      (tendsto_natCast_atTop_atTop.comp hm)
  have hUpper : Tendsto (fun n : ℕ ↦ (C*A^2)*((Real.log (m n:ℝ))^(2:ℝ) / (m n:ℝ)^(1/8:ℝ)) +
      (S*√A)*((Real.log (m n:ℝ))^(1/2:ℝ) / (m n:ℝ)^(1/8:ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero,add_zero] using ((hLogRatio 2).const_mul (C*A^2)).add
      ((hLogRatio (1/2)).const_mul (S*√A))
  apply squeeze_zero' _ _ hUpper
  · exact Eventually.of_forall (fun n ↦ by positivity)
  · filter_upwards [hv,hm.eventually_ge_atTop (1:ℕ)] with n hn hn1
    have hx : 0 ≤ (m n:ℝ) := by positivity
    have hln : 0 ≤ Real.log (m n:ℝ) := Real.log_nonneg (by exact_mod_cast hn1)
    have hrwn : (m n:ℝ)^(-(1/8:ℝ)) = ((m n:ℝ)^(1/8:ℝ))⁻¹ :=
      Real.rpow_neg hx _
    have hvs : (√(v n))^2 = v n := Real.sq_sqrt hn.1
    have hs : √(v n) ≤ √A * √(Real.log (m n:ℝ)) := by
      rw [← Real.sqrt_mul hA]
      exact Real.sqrt_le_sqrt hn.2
    have hPow : v n ^ 2 ≤ (A*Real.log (m n:ℝ))^2 := pow_le_pow_left₀ hn.1 hn.2 _
    rw [Real.rpow_ofNat (Real.log (m n:ℝ)) 2, ← Real.sqrt_eq_rpow, hrwn]
    calc
      _ = ((m n:ℝ)^(1/8:ℝ))⁻¹ * (C*((√(v n))^2)^2 + S*√(v n)) := by ring
      _ = ((m n:ℝ)^(1/8:ℝ))⁻¹ * (C*(v n)^2 + S*√(v n)) := by rw [hvs]
      _ ≤ ((m n:ℝ)^(1/8:ℝ))⁻¹ * (C*(A*Real.log (m n:ℝ))^2 + S*(√A*√(Real.log (m n:ℝ)))) := by
        exact mul_le_mul_of_nonneg_left
          (add_le_add (mul_le_mul_of_nonneg_left hPow hC) (mul_le_mul_of_nonneg_left hs hS)) (by positivity)
      _ = _ := by simp only [div_eq_mul_inv]; ring


private theorem cube_scale (n : ℝ) (hn : 0 < n) :
    n*(n^(-(1/2:ℝ)))^3 = n^(-(1/2:ℝ)) := by
  have he := Real.rpow_mul hn.le (-(1/2:ℝ)) (3:ℝ)
  rw [Real.rpow_ofNat] at he
  rw [← he, mul_comm n, ← Real.rpow_add_one hn.ne']
  congr 1
  norm_num

/-- The true weighted error tends to zero after multiplication by sqrt(v):
explicit third moments scale as (sqrt(v)/sqrt(n))³ and the Gaussian
strip coefficient has an eventual finite bound. No constraint on the
off-diagonal rank or conditioning appears. -/
theorem actual_winner_weight_rate_zero_along_dimensions (m : ℕ→ℕ) (hm : Tendsto m atTop atTop) (v third strip : ℕ → ℝ) (A C S K : ℝ)
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hS : 0 ≤ S) (hK : 0 ≤ K)
    (hv : ∀ᶠ n in atTop, 0 ≤ v n ∧ v n ≤ A*Real.log (m n:ℝ))
    (hT : ∀ᶠ n in atTop, 0 ≤ third n ∧
      third n ≤ C*(√(v n)*(m n:ℝ)^(-(1/2:ℝ)))^3)
    (hS' : ∀ᶠ n in atTop, 0 ≤ strip n ∧ strip n ≤ S) :
    Tendsto (fun n : ℕ ↦ √(v n)*(((m n:ℝ)*K/((m n:ℝ)^(-(1/8:ℝ)))^3)*third n +
      (m n:ℝ)^(-(1/8:ℝ))*strip n)) atTop (𝓝 0) := by
  apply squeeze_zero' _ _ (fixed_face_weighted_rate_zero_along_dimensions m hm v A (K*C) S hA (mul_nonneg hK hC) hS hv)
  · filter_upwards [hT,hS'] with n ht hs
    exact mul_nonneg (Real.sqrt_nonneg _) (add_nonneg
      (mul_nonneg (by positivity) ht.1) (mul_nonneg (by positivity) hs.1))
  · filter_upwards [hT,hS',hm.eventually_ge_atTop (1:ℕ)] with n ht hs hn
    have hn' : 0 < (m n:ℝ) := by exact_mod_cast (show 0<m n by omega)
    apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
    let t := (m n:ℝ)^(-(1/8:ℝ))
    let s := (m n:ℝ)^(-(1/2:ℝ))
    have ht' : 0 < t := Real.rpow_pos_of_pos hn' _
    have hns : (m n:ℝ)*s^3=s := cube_scale _ hn'
    have hst : s/t^3=t := smoothing_delta_cubic_rate _ hn'
    change ((m n:ℝ)*K/t^3)*third n+t*strip n ≤ t*(K*C*(√(v n))^3+S)
    calc
      _ ≤ ((m n:ℝ)*K/t^3)*(C*(√(v n)*s)^3)+t*S :=
        add_le_add (mul_le_mul_of_nonneg_left ht.2 (by positivity))
          (mul_le_mul_of_nonneg_left hs.2 ht'.le)
      _ = (s/t^3)*(K*C*(√(v n))^3)+t*S := by
        calc
          _ = (((m n:ℝ)*s^3)/t^3)*(K*C*(√(v n))^3)+t*S := by ring
          _ = _ := by rw [hns]
      _ = _ := by rw [hst]; ring

#print axioms fixed_face_weighted_rate_zero_along_dimensions
#print axioms actual_winner_weight_rate_zero_along_dimensions
end CubeSqrtProbability
