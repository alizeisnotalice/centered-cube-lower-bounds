import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace CubeSqrtProbability
theorem actual_amplitude_scale {n K v p : ℝ}
    (hn : 0<n) (hK : 0<K) (hv : 0≤v) (hp : 0≤p)
    (hs : n*p^2=(29/9)*K^2*v) :
    8*(7*|p|/K)≤112*(√v*n^(-(1/2:ℝ))) := by
  have he : (p/K)^2=(29/9)*(v/n) := by
    calc
      _ = (n*p^2)/(n*K^2) := by field_simp
      _ = _ := by rw [hs]; field_simp
  have hz : 0≤v/n := div_nonneg hv hn.le
  have hle : p/K≤2*√(v/n) := by
    apply (sq_le_sq₀ (div_nonneg hp hK.le)
      (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))).mp
    rw [he,mul_pow,Real.sq_sqrt hz]
    nlinarith only [hz]
  have e : n^(-(1/2:ℝ)) = (√n)⁻¹ := by
    rw [Real.rpow_neg hn.le,Real.sqrt_eq_rpow]
  rw [abs_of_nonneg hp,e]
  rw [Real.sqrt_div hv,div_eq_mul_inv] at hle
  rw [show 8*(7*p/K)=56*(p/K) by ring,show 112*(√v*(√n)⁻¹)=56*(2*(√v*(√n)⁻¹)) by ring]
  exact mul_le_mul_of_nonneg_left hle (by norm_num)
end CubeSqrtProbability
#print axioms CubeSqrtProbability.actual_amplitude_scale
