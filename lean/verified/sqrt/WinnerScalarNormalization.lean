import TrueTiltCrossLimits

open Filter
open scoped Topology
namespace CubeSqrtProbability

theorem eventually_abs_le_of_tendsto_real {f : ℕ → ℝ} {c : ℝ}
    (h : Tendsto f atTop (𝓝 c)) : ∀ᶠ n in atTop, |f n| ≤ |c|+1 := by
  have he := Metric.tendsto_nhds.mp h 1 (by norm_num)
  filter_upwards [he] with n hn
  rw [Real.dist_eq] at hn
  calc
    _ = |(f n-c)+c| := by congr 1; ring
    _ ≤ |f n-c|+|c| := abs_add_le _ _
    _ ≤ _ := by linarith

theorem winner_anchor_normalization (v V : ℕ → ℝ)
    (hv : Tendsto v atTop atTop)
    {C : ℝ} (hV : ∀ᶠ n in atTop, |V n-v n|≤C) :
    Tendsto V atTop atTop ∧ Tendsto (fun n ↦ √(v n)/√(V n)) atTop (𝓝 1) := by
  have hGrow : Tendsto V atTop atTop := by
    refine tendsto_atTop.mpr fun b ↦ ?_
    filter_upwards [hV,hv.eventually_gt_atTop (b+C)] with n hn hp
    linarith [(abs_le.mp hn).1]
  refine ⟨hGrow, ?_⟩
  have hs : Tendsto (fun n ↦ (v n-V n)/V n) atTop (𝓝 0) := by
    have hi := tendsto_inv_atTop_zero.comp hGrow
    refine squeeze_zero_norm' ?_ (by simpa using hi.const_mul C)
    filter_upwards [hV,hGrow.eventually_gt_atTop 0] with n hn hp
    rw [Real.norm_eq_abs,abs_div,abs_of_pos hp,abs_sub_comm,div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hn (by positivity)
  have hrat : Tendsto (fun n ↦ v n/V n) atTop (𝓝 1) := by
    have hs' := hs.const_add 1
    apply (by simpa using hs' : Tendsto (fun n ↦ 1+(v n-V n)/V n) atTop (𝓝 1)).congr'
    filter_upwards [hGrow.eventually_gt_atTop 0] with n h
    field_simp
    ring
  have hsqrt := Real.continuous_sqrt.tendsto 1 |>.comp hrat
  have hS : Tendsto (fun n ↦ √(v n/V n)) atTop (𝓝 1) := by simpa [Function.comp_def] using hsqrt
  apply hS.congr'
  filter_upwards [hv.eventually_gt_atTop 0] with n hn
  exact Real.sqrt_div hn.le (V n)

end CubeSqrtProbability
#print axioms CubeSqrtProbability.eventually_abs_le_of_tendsto_real
#print axioms CubeSqrtProbability.winner_anchor_normalization
