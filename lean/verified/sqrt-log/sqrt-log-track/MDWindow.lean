import Mathlib

namespace CubeMD

theorem window_root_le (n z K : ℝ) (hz : 0 ≤ z) (_hK : 0 ≤ K)
    (hwin : z ^ 6 ≤ n) (hN : K ^ 3 ≤ n) :
    K * z ≤ Real.sqrt n := by
  have hn : 0 ≤ n := (by positivity : 0 ≤ z ^ 6).trans hwin
  have hs : 0 ≤ Real.sqrt n := Real.sqrt_nonneg n
  have hz3 : z ^ 3 ≤ Real.sqrt n := by
    apply le_of_sq_le_sq _ hs
    rw [Real.sq_sqrt hn]
    convert hwin using 1 <;> ring
  apply le_of_pow_le_pow_left₀ (by decide : (3 : ℕ) ≠ 0) hs
  calc
    (K * z) ^ 3 = K ^ 3 * z ^ 3 := mul_pow _ _ _
    _ ≤ n * z ^ 3 := mul_le_mul_of_nonneg_right hN (by positivity)
    _ ≤ n * Real.sqrt n := mul_le_mul_of_nonneg_left hz3 hn
    _ = Real.sqrt n ^ 3 := by rw [pow_succ, Real.sq_sqrt hn]

end CubeMD
#print axioms CubeMD.window_root_le
