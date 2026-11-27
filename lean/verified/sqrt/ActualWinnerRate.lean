import ActualWinnerWeightEstimate
import FixedFaceRate

open Filter
open scoped Topology
namespace CubeSqrtProbability

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
theorem actual_winner_weight_rate_zero (v third strip : ℕ → ℝ) (A C S K : ℝ)
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hS : 0 ≤ S) (hK : 0 ≤ K)
    (hv : ∀ᶠ n in atTop, 0 ≤ v n ∧ v n ≤ A*Real.log (n:ℝ))
    (hT : ∀ᶠ n in atTop, 0 ≤ third n ∧
      third n ≤ C*(√(v n)*(n:ℝ)^(-(1/2:ℝ)))^3)
    (hS' : ∀ᶠ n in atTop, 0 ≤ strip n ∧ strip n ≤ S) :
    Tendsto (fun n : ℕ ↦ √(v n)*(((n:ℝ)*K/((n:ℝ)^(-(1/8:ℝ)))^3)*third n +
      (n:ℝ)^(-(1/8:ℝ))*strip n)) atTop (𝓝 0) := by
  apply squeeze_zero' _ _ (fixed_face_weighted_rate_zero v A (K*C) S hA (mul_nonneg hK hC) hS hv)
  · filter_upwards [hT,hS'] with n ht hs
    exact mul_nonneg (Real.sqrt_nonneg _) (add_nonneg
      (mul_nonneg (by positivity) ht.1) (mul_nonneg (by positivity) hs.1))
  · filter_upwards [hT,hS',eventually_ge_atTop (1:ℕ)] with n ht hs hn
    have hn' : 0 < (n:ℝ) := by exact_mod_cast (show 0<n by omega)
    apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
    let t := (n:ℝ)^(-(1/8:ℝ))
    let s := (n:ℝ)^(-(1/2:ℝ))
    have ht' : 0 < t := Real.rpow_pos_of_pos hn' _
    have hns : (n:ℝ)*s^3=s := cube_scale _ hn'
    have hst : s/t^3=t := smoothing_delta_cubic_rate _ hn'
    change ((n:ℝ)*K/t^3)*third n+t*strip n ≤ t*(K*C*(√(v n))^3+S)
    calc
      _ ≤ ((n:ℝ)*K/t^3)*(C*(√(v n)*s)^3)+t*S :=
        add_le_add (mul_le_mul_of_nonneg_left ht.2 (by positivity))
          (mul_le_mul_of_nonneg_left hs.2 ht'.le)
      _ = (s/t^3)*(K*C*(√(v n))^3)+t*S := by
        calc
          _ = (((n:ℝ)*s^3)/t^3)*(K*C*(√(v n))^3)+t*S := by ring
          _ = _ := by rw [hns]
      _ = _ := by rw [hst]; ring

end CubeSqrtProbability
#print axioms CubeSqrtProbability.actual_winner_weight_rate_zero
