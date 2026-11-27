import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

open Filter
open scoped Topology

namespace CubeSqrtProbability

theorem smoothing_delta_cubic_rate (n : ℝ) (hn : 0 < n) :
    (n^(-(1/2:ℝ))) / (n^(-(1/8:ℝ)))^3 = n^(-(1/8:ℝ)) := by
  have he := Real.rpow_mul hn.le (-(1/8:ℝ)) (3:ℝ)
  rw [Real.rpow_ofNat] at he
  rw [← he, ← Real.rpow_sub hn]
  congr 1
  norm_num

/-- For v=O(log n), the fixed-face rate after choosing η=n^(-1/8)
is little o of 1/sqrt(v), as required by the weighted winning integral. -/
theorem fixed_face_weighted_rate_zero (v : ℕ → ℝ) (A C S : ℝ)
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hS : 0 ≤ S)
    (hv : ∀ᶠ n in atTop, 0 ≤ v n ∧ v n ≤ A*Real.log (n:ℝ)) :
    Tendsto (fun n : ℕ ↦
      Real.sqrt (v n) * ((n:ℝ)^(-(1/8:ℝ)) * (C*(Real.sqrt (v n))^3 + S))) atTop (𝓝 0) := by
  have hLogRatio (p : ℝ) :
      Tendsto (fun n : ℕ ↦ (Real.log (n:ℝ))^p / (n:ℝ)^(1/8:ℝ)) atTop (𝓝 0) :=
    (isLittleO_log_rpow_rpow_atTop p (show (0:ℝ) < 1/8 by norm_num)).tendsto_div_nhds_zero.comp
      tendsto_natCast_atTop_atTop
  have hUpper : Tendsto (fun n : ℕ ↦ (C*A^2)*((Real.log (n:ℝ))^(2:ℝ) / (n:ℝ)^(1/8:ℝ)) +
      (S*√A)*((Real.log (n:ℝ))^(1/2:ℝ) / (n:ℝ)^(1/8:ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero,add_zero] using ((hLogRatio 2).const_mul (C*A^2)).add
      ((hLogRatio (1/2)).const_mul (S*√A))
  apply squeeze_zero' _ _ hUpper
  · exact Eventually.of_forall (fun n ↦ by positivity)
  · filter_upwards [hv,eventually_ge_atTop (1:ℕ)] with n hn hn1
    have hx : 0 ≤ (n:ℝ) := by positivity
    have hln : 0 ≤ Real.log (n:ℝ) := Real.log_nonneg (by exact_mod_cast hn1)
    have hrwn : (n:ℝ)^(-(1/8:ℝ)) = ((n:ℝ)^(1/8:ℝ))⁻¹ :=
      Real.rpow_neg hx _
    have hvs : (√(v n))^2 = v n := Real.sq_sqrt hn.1
    have hs : √(v n) ≤ √A * √(Real.log (n:ℝ)) := by
      rw [← Real.sqrt_mul hA]
      exact Real.sqrt_le_sqrt hn.2
    have hPow : v n ^ 2 ≤ (A*Real.log (n:ℝ))^2 := pow_le_pow_left₀ hn.1 hn.2 _
    rw [Real.rpow_ofNat (Real.log (n:ℝ)) 2, ← Real.sqrt_eq_rpow, hrwn]
    calc
      _ = ((n:ℝ)^(1/8:ℝ))⁻¹ * (C*((√(v n))^2)^2 + S*√(v n)) := by ring
      _ = ((n:ℝ)^(1/8:ℝ))⁻¹ * (C*(v n)^2 + S*√(v n)) := by rw [hvs]
      _ ≤ ((n:ℝ)^(1/8:ℝ))⁻¹ * (C*(A*Real.log (n:ℝ))^2 + S*(√A*√(Real.log (n:ℝ)))) := by
        exact mul_le_mul_of_nonneg_left
          (add_le_add (mul_le_mul_of_nonneg_left hPow hC) (mul_le_mul_of_nonneg_left hs hS)) (by positivity)
      _ = _ := by simp only [div_eq_mul_inv]; ring

end CubeSqrtProbability
#print axioms CubeSqrtProbability.fixed_face_weighted_rate_zero
