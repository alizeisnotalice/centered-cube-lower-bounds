import AsymptoticRounding

open Filter
open scoped Topology

namespace CenteredCube.RudinDensity

theorem paperU_rescale {n : ℕ} (hn : 2 ≤ n) (hK : 0 < paperK n) :
    paperU n = Real.sqrt (Real.log (n:ℝ)) * (paperA n/(paperK n:ℝ)) := by
  have hn' : (1:ℝ) < (n:ℝ) := by exact_mod_cast (show 1 < n by omega)
  have hL : 0 < Real.log (n:ℝ) := Real.log_pos hn'
  have hL0 : Real.sqrt (Real.log (n:ℝ)) ≠ 0 := (Real.sqrt_pos.2 hL).ne'
  have hK0 : (paperK n:ℝ) ≠ 0 := by exact_mod_cast hK.ne'
  unfold paperU paperA
  field_simp [Real.pi_pos.ne']

theorem rounded_height_error {n : ℕ} (hn : 2 ≤ n) (ha : 4 ≤ paperA n) :
    |paperU n ^ 2 - Real.log (n:ℝ)| ≤ 20 * Real.log (n:ℝ)/paperA n := by
  let A := paperA n
  let K : ℝ := paperK n
  let L := Real.log (n:ℝ)
  have hL : 0 < L := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hA0 : 0 < A := by linarith only [ha]
  have hd : |K-A| ≤ 2 := roundedFour_error hA0.le
  have hk := abs_le.mp hd
  have hkL : A/2 ≤ K := by linarith only [ha, hk.1]
  have hkU : K ≤ 3*A/2 := by linarith only [ha, hk.2]
  have hK0 : 0 < K := (half_pos hA0).trans_le hkL
  have hKn : 0 < paperK n := by change (0:ℝ) < (paperK n:ℝ) at hK0; exact_mod_cast hK0
  have hU := paperU_rescale hn hKn
  change paperU n = Real.sqrt L * (A/K) at hU
  have e : paperU n^2-L = L*((A-K)*(A+K))/K^2 := by
    rw [hU,mul_pow,Real.sq_sqrt hL.le,div_pow]
    field_simp [hK0.ne']
    <;> ring
  change |paperU n^2-L| ≤ 20*L/A
  rw [e,abs_div,abs_mul,abs_mul,abs_of_pos hL,abs_of_pos (show 0 < K^2 by positivity),
    abs_of_pos (add_pos hA0 hK0),abs_sub_comm A K]
  apply (div_le_iff₀ (show 0 < K^2 by positivity)).2
  have hP : L*(|K-A| *(A+K)) ≤ L*(2*(5*A/2)) := by
    apply mul_le_mul_of_nonneg_left _ hL.le
    exact mul_le_mul hd (by linarith only [hkU]) (by positivity) (by norm_num)
  have hSq : A^2/4 ≤ K^2 := by
    have hs := pow_le_pow_left₀ (half_pos hA0).le hkL 2
    linarith only [hs]
  have hMul := mul_le_mul_of_nonneg_left hSq (show 0 ≤ 20*L/A by positivity)
  have he : (20*L/A)*(A^2/4) = L*(2*(5*A/2)) := by field_simp; ring
  rw [he] at hMul
  exact hP.trans hMul

theorem rounded_height_error_zero :
    Tendsto (fun n : ℕ => |paperU n ^ 2 - Real.log (n:ℝ)|) atTop (𝓝 0) := by
  have H : Tendsto (fun n : ℕ => 20*Real.log (n:ℝ)/paperA n) atTop (𝓝 0) := by
    simpa only [mul_zero, mul_div_assoc] using log_div_paperA_zero.const_mul 20
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds H ?_ ?_
  · exact Eventually.of_forall (fun _ => abs_nonneg _)
  · filter_upwards [eventually_ge_atTop (2:ℕ),paperA_tends_top.eventually_ge_atTop 4] with n hn hA
    exact rounded_height_error hn hA

end CenteredCube.RudinDensity

#print axioms CenteredCube.RudinDensity.rounded_height_error
#print axioms CenteredCube.RudinDensity.rounded_height_error_zero
