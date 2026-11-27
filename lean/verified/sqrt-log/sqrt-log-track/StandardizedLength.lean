import Mathlib
open Set
namespace CubeMD
theorem standardized_strip_length (q y r v : ℝ) (hy : 0 < y) (hr : 0 < r)
    (hql : 2 * y / 3 ≤ q) (hqu : q ≤ 2 * y) (hv : v ∈ Icc (1/2 : ℝ) (3/2)) :
    1 / (Real.sqrt 6 * (y * r)) ≤ 1 / (q * (r * Real.sqrt v)) ∧
    1 / (q * (r * Real.sqrt v)) ≤ 3 / (y * r) := by
  have hv0 : 0 < v := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1/2) hv.1
  have hs : 0 < Real.sqrt v := Real.sqrt_pos.2 hv0
  have hq : 0 < q := lt_of_lt_of_le (by positivity) hql
  have h1 : 1 ≤ 2 * Real.sqrt v := by
    nlinarith [Real.sq_sqrt hv0.le, hv.1, sq_nonneg (Real.sqrt v - 1)]
  have h2 : 2 * Real.sqrt v ≤ Real.sqrt 6 := by
    apply le_of_sq_le_sq _ (by positivity)
    nlinarith [Real.sq_sqrt hv0.le, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 6), hv.2]
  have ha : q * (r * Real.sqrt v) ≤ Real.sqrt 6 * (y * r) := calc
    _ ≤ (2 * y) * (r * Real.sqrt v) := mul_le_mul_of_nonneg_right hqu (by positivity)
    _ = (2 * Real.sqrt v) * (y * r) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right h2 (by positivity)
  have hb : y * r ≤ 3 * (q * (r * Real.sqrt v)) := calc
    _ ≤ (2 * Real.sqrt v) * (y * r) := by nlinarith [mul_le_mul_of_nonneg_right h1 (show 0 ≤ y*r by positivity)]
    _ = (2 * y / 3) * (3 * (r * Real.sqrt v)) := by ring
    _ ≤ _ := by simpa [mul_comm, mul_assoc, mul_left_comm] using mul_le_mul_of_nonneg_right hql (show 0 ≤ 3 * (r * Real.sqrt v) by positivity)
  constructor
  · exact one_div_le_one_div_of_le (by positivity) ha
  · exact (div_le_div_iff₀ (by positivity) (by positivity)).2 (by simpa using hb)
end CubeMD
#print axioms CubeMD.standardized_strip_length
