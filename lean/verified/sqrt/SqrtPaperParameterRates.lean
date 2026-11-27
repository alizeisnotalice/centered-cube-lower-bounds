import SqrtPaperMeshChoice
import SqrtKernelBudgetLimits
import SqrtPaperCrossRateSource

namespace CenteredCubeSqrt
open Filter Set
open scoped Topology BigOperators
set_option maxHeartbeats 2000000

theorem sum_range_succ_eq_Icc (M : ℕ) (f : ℕ→ℝ) :
    (∑ j ∈ Finset.range M, f (j+1))=∑ j ∈ Finset.Icc 1 M,f j := by
  rw [←Finset.Ico_succ_right_eq_Icc,Finset.sum_Ico_eq_sum_range, show Order.succ M-1=M by change M+1-1=M; omega]
  simp only [add_comm]

theorem manuscriptCrossError_eq_coarse (B K : ℝ) (M : ℕ) :
    manuscriptCrossError B K M = CubeSqrtEnd.coarsePaperCross (1-1/B) K M := by
  unfold manuscriptCrossError CubeSqrtEnd.coarsePaperCross
  congr 2
  · rw [←sum_range_succ_eq_Icc M (fun m => ((m:ℝ)^2)⁻¹)]
    simp only [Nat.cast_add,Nat.cast_one,one_div]
  · rw [←sum_range_succ_eq_Icc M (fun m => (m:ℝ)⁻¹)]
    simp only [Nat.cast_add,Nat.cast_one,one_div]

noncomputable def paperAtomicCrossSmoothing (w K B v : ℝ) (M : ℕ) : ℝ :=
  (2/3)*K*paperMeshDelta w K v + manuscriptCrossError B K M

theorem actual_cross_smoothing_rate {w : ℝ} (hw : 4≤w) {v : ℕ→ℝ} {b d : ℕ→ℕ}
    (h : ∀ᶠ n in atTop, PaperMeshParameters w (v n) (b n) (d n))
    (hK : Tendsto (fun n => (paperPeriod (d n):ℝ)/(v n)^4) atTop atTop) :
    Tendsto (fun n => v n*paperAtomicCrossSmoothing w (paperPeriod (d n):ℝ) ((2:ℝ)^(b n))
      (v n) (paperMeshM (v n))) atTop (𝓝 (2/(3*w))) := by
  let B (n : ℕ) := (2:ℝ)^(b n)
  let K (n : ℕ) := (paperPeriod (d n):ℝ)
  let M (n : ℕ) := paperMeshM (v n)
  have ha : ∀ᶠ n in atTop, 0≤1-1/B n ∧ 1-1/B n≤1 := h.mono fun n H => by
    have hp : 0<B n := by dsimp [B]; positivity
    have hb : 1≤B n := by linarith [H.label_lower,H.v_ge_four]
    exact ⟨sub_nonneg.mpr ((div_le_iff₀ hp).2 (by linarith)),
      sub_le_self _ (by positivity)⟩
  have hK' : ∀ᶠ n in atTop, 1≤K n := h.mono fun n H => by
    have hn : 1≤paperPeriod (d n) := by have := H.period_lower; omega
    dsimp [K]
    exact_mod_cast hn
  have hv : ∀ᶠ n in atTop, 0<v n := h.mono fun _ H => by linarith [H.v_ge_four]
  have hM : ∀ᶠ n in atTop, (M n:ℝ)≤v n := h.mono fun _ H => H.mesh_le_v
  have hwp : 0<w := by linarith
  have H := CubeSqrtEnd.coarsePaperCross_with_smoothing_tendsto hwp ha hK' hv hM hK
  apply H.congr'
  filter_upwards [h,hv] with n hn vn
  have kk : 0<K n := by
    dsimp [K]
    exact_mod_cast (show 0<paperPeriod (d n) by have := hn.period_lower; omega)
  change v n*(CubeSqrtEnd.coarsePaperCross (1-1/B n) (K n) (M n)+2/(3*w*v n)) =
    v n*paperAtomicCrossSmoothing w (K n) (B n) (v n) (M n)
  rw [paperAtomicCrossSmoothing,manuscriptCrossError_eq_coarse]
  congr 1
  unfold paperMeshDelta
  field_simp [hwp.ne',kk.ne',vn.ne']
  ring

theorem paper_mesh_scaled_vanishing {w : ℝ} {v : ℕ→ℝ} {b d : ℕ→ℕ}
    (h : ∀ᶠ n in atTop, PaperMeshParameters w (v n) (b n) (d n))
    (hv : Tendsto v atTop atTop)
    (hK : Tendsto (fun n => (paperPeriod (d n):ℝ)/v n) atTop atTop) :
    Tendsto (fun n => v n/((2:ℝ)^(b n))^2) atTop (𝓝 0) ∧
    Tendsto (fun n => v n/(paperPeriod (d n):ℝ)) atTop (𝓝 0) ∧
    Tendsto (fun n => v n/((paperMeshM (v n):ℕ):ℝ)^3) atTop (𝓝 0) := by
  let B (n : ℕ) := (2:ℝ)^(b n)
  let M (n : ℕ) := (paperMeshM (v n):ℝ)
  have htB : Tendsto B atTop atTop := tendsto_atTop_mono' atTop (h.mono fun _ H => H.label_lower) hv
  have htM : Tendsto M atTop atTop :=
    tendsto_atTop_mono' atTop (h.mono fun _ H => H.mesh_sqrt_lower) (Real.tendsto_sqrt_atTop.comp hv)
  have hiB := tendsto_inv_atTop_zero.comp htB
  have hiM := tendsto_inv_atTop_zero.comp htM
  have hiK := tendsto_inv_atTop_zero.comp hK
  constructor
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hiB ?_ ?_
    · exact h.mono fun n H => div_nonneg (by linarith [H.v_ge_four]) (sq_nonneg _)
    · filter_upwards [h] with n H
      have hb : 0<B n := by dsimp [B]; positivity
      have E := div_le_div_of_nonneg_right H.label_lower (sq_nonneg (B n))
      change v n/(B n)^2≤B n/(B n)^2 at E
      change v n/(B n)^2≤(B n)⁻¹
      refine E.trans_eq ?_
      field_simp
  constructor
  · simpa only [Function.comp_def,inv_div] using hiK
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hiM ?_ ?_
    · exact h.mono fun n H => div_nonneg (by linarith [H.v_ge_four]) (by positivity)
    · filter_upwards [h] with n H
      have hb : 0<M n := by dsimp [M]; exact_mod_cast H.mesh_lower
      have hs : v n≤(M n)^2 := by
        have P := pow_le_pow_left₀ (Real.sqrt_nonneg (v n)) H.mesh_sqrt_lower 2
        rw [Real.sq_sqrt (by linarith [H.v_ge_four])] at P
        exact P
      have E := div_le_div_of_nonneg_right hs (pow_nonneg hb.le 3)
      change v n/(M n)^3≤(M n)⁻¹
      refine E.trans_eq ?_
      field_simp

#print axioms actual_cross_smoothing_rate
#print axioms paper_mesh_scaled_vanishing
end CenteredCubeSqrt
