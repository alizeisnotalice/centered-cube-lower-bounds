import ActualPaperPairBound
import SqrtPaperBudgetEligibility

namespace CenteredCubeSqrt
open Filter Set
open scoped Topology

theorem actual_pair_near_error_scaled {w : ℝ} (hw : 4≤w) {v : ℕ→ℝ} {b d : ℕ→ℕ}
    (h : ∀ᶠ n in atTop, PaperMeshParameters w (v n) (b n) (d n))
    (hv : Tendsto v atTop atTop)
    (hK : Tendsto (fun n => (paperPeriod (d n):ℝ)/(v n)^4) atTop atTop)
    (hK1 : Tendsto (fun n => (paperPeriod (d n):ℝ)/v n) atTop atTop) :
    Tendsto (fun n =>
       let K := (paperPeriod (d n):ℝ)
       let B := (2:ℝ)^(b n)
       let M := paperMeshM (v n)
       let δ := paperMeshDelta w K (v n)
       v n*actualPairNearError B K M δ) atTop (𝓝 (2/(3*w))) := by
  have X := paper_mesh_scaled_vanishing h hv hK1
  have Y := actual_cross_smoothing_rate hw h hK
  have Z := ((X.1.const_mul (2/3:ℝ)).add (X.2.1.const_mul 2)).add Y
  simp only [mul_zero,zero_add] at Z
  apply Z.congr
  intro n
  dsimp [actualPairNearError,paperAtomicCrossSmoothing]
  ring

theorem actual_pair_relative_error_scaled {w : ℝ} (hw : 4≤w) {v : ℕ→ℝ} {b d : ℕ→ℕ}
    (h : ∀ᶠ n in atTop, PaperMeshParameters w (v n) (b n) (d n))
    (hv : Tendsto v atTop atTop)
    (hK : Tendsto (fun n => (paperPeriod (d n):ℝ)/(v n)^4) atTop atTop)
    (hK1 : Tendsto (fun n => (paperPeriod (d n):ℝ)/v n) atTop atTop) :
    Tendsto (fun n =>
       let K := (paperPeriod (d n):ℝ)
       let B := (2:ℝ)^(b n)
       let M := paperMeshM (v n)
       let δ := paperMeshDelta w K (v n)
       v n*actualPairRelativeError B K M δ) atTop (𝓝 (87/(50*w))) := by
  apply (paper_actual_relative_error_scaled hw h hv hK hK1).congr
  intro n
  dsimp [actualPairRelativeError,paperAtomicCrossSmoothing,paperKernelRelError,
    paperDiagonalBudget,paperPlateauTail]
  ring

theorem actual_pair_dimension_conditions {p w : ℝ} (hp : 0<p) (hw : 4≤w) {v : ℕ→ℝ} {b d : ℕ→ℕ}
    (h : ∀ᶠ n in atTop, PaperMeshParameters w (v n) (b n) (d n))
    (hv : Tendsto v atTop atTop)
    (hK : Tendsto (fun n => (paperPeriod (d n):ℝ)/(v n)^4) atTop atTop)
    (hK1 : Tendsto (fun n => (paperPeriod (d n):ℝ)/v n) atTop atTop)
    (hK0 : Tendsto (fun n => (paperPeriod (d n):ℝ)) atTop atTop) :
    ∀ᶠ n in atTop,
      let K := (paperPeriod (d n):ℝ)
      let B := (2:ℝ)^(b n)
      let M := paperMeshM (v n)
      let δ := paperMeshDelta w K (v n)
      7*p/K≤1/8 ∧ v n*actualPairRelativeError B K M δ≤1 ∧
      4*v n/5≤(v n-1)/(1+7*p/K) ∧ 8*v n*actualPairNearError B K M δ≤2 := by
  let K (n : ℕ) := (paperPeriod (d n):ℝ)
  let B (n : ℕ) := (2:ℝ)^(b n)
  let M := fun n => paperMeshM (v n)
  let δ := fun n => paperMeshDelta w (K n) (v n)
  have hw0 : 0<w := by linarith
  have hN := (actual_pair_near_error_scaled hw h hv hK hK1).eventually_lt_const
    (show 2/(3*w)<1/4 from (div_lt_iff₀ (by positivity)).2 (by linarith))
  have hR := (actual_pair_relative_error_scaled hw h hv hK hK1).eventually_lt_const
    (show 87/(50*w)<1 from (div_lt_iff₀ (by positivity)).2 (by linarith))
  have hAK : Tendsto (fun n => 7*p/K n) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero,Function.comp_apply,K] using (tendsto_inv_atTop_zero.comp hK0).const_mul (7*p)
  have hKpos := (tendsto_atTop.1 hK0) 1
  have hv10 := (tendsto_atTop.1 hv) 10
  filter_upwards [hN,hR,hAK.eventually_lt_const (by norm_num : (0:ℝ)<1/8), hKpos, hv10]
    with n hN hR hAK hKpos hv10
  dsimp only
  change 1≤K n at hKpos
  change v n*actualPairNearError (B n) (K n) (M n) (δ n)<1/4 at hN
  change v n*actualPairRelativeError (B n) (K n) (M n) (δ n)<1 at hR
  change 7*p/K n≤1/8 ∧ v n*actualPairRelativeError (B n) (K n) (M n) (δ n)≤1 ∧
      4*v n/5≤(v n-1)/(1+7*p/K n) ∧ 8*v n*actualPairNearError (B n) (K n) (M n) (δ n)≤2
  refine ⟨hAK.le,hR.le,?_,?_⟩
  · have hA0 : 0≤7*p/K n := by positivity
    apply (le_div_iff₀ (by positivity)).2
    have hT := mul_le_mul_of_nonneg_left (show 1+7*p/K n≤9/8 by linarith) (by linarith : 0≤4*v n/5)
    linarith only [hT,hv10]
  · linarith

#print axioms actual_pair_dimension_conditions
end CenteredCubeSqrt
