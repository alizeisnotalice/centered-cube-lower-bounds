import SqrtActualFarNormalized

namespace CenteredCubeSqrt
open Set MeasureTheory Filter Topology
open scoped BigOperators Interval
set_option maxHeartbeats 750000

theorem normalized_kernel_uniform_far_margin {κ Q E V : ℝ}
    (hQ : Q≤21/500) (hE : E≤1/1000) (hV : 19/50≤V)
    (hκ : -(4*Q+1/116+E)/V≤κ ∧ κ≤(4*Q+34/261+E)/V) :
    -(1/2:ℝ)≤κ ∧ 1/5≤1-κ := by
  have v : 0<V := by linarith
  have hi : (4*Q+34/261+E)/V≤4/5 := (div_le_iff₀ v).2 (by linarith)
  have lo : -(1/2:ℝ)≤ -(4*Q+1/116+E)/V := (le_div_iff₀ v).2 (by linarith)
  exact ⟨lo.trans hκ.1,by linarith [hκ.2.trans hi]⟩

theorem normalized_kernel_uniform_near_margin {κ E τ : ℝ} (hE : E≤1/1000)
    (hlo : -(34/121:ℝ)-8*E≤κ)
    (hmid : 1/8≤τ → 14703/61952-8*E≤1-κ) :
    -(1/2:ℝ)≤κ ∧ (1/8≤τ → 1/5≤1-κ) := by
  exact ⟨by linarith,fun h => by linarith [hmid h]⟩

theorem normalized_kernel_eventually_finite_budgets {Q E EN V : ℕ→ℝ}
    (hQ : Tendsto Q atTop (𝓝 (1/24))) (hE : Tendsto E atTop (𝓝 0))
    (hEN : Tendsto EN atTop (𝓝 0)) (hV : Tendsto V atTop (𝓝 (100/261))) :
    ∀ᶠ n in atTop, Q n≤21/500 ∧ E n≤1/1000 ∧ EN n≤1/1000 ∧ 19/50≤V n := by
  have hQ' := hQ.eventually_lt_const (show (1:ℝ)/24<21/500 by norm_num)
  have hE' := hE.eventually_lt_const (show (0:ℝ)<1/1000 by norm_num)
  have hEN' := hEN.eventually_lt_const (show (0:ℝ)<1/1000 by norm_num)
  have hV' := hV.eventually_const_lt (show (19:ℝ)/50<100/261 by norm_num)
  filter_upwards [hQ',hE',hEN',hV'] with n a b c d
  exact ⟨a.le,b.le,c.le,d.le⟩

#print axioms normalized_kernel_eventually_finite_budgets
#print axioms normalized_kernel_uniform_far_margin
#print axioms normalized_kernel_uniform_near_margin
end CenteredCubeSqrt
