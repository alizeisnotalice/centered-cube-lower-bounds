import AllIntegerPacketOverlap
import PacketGapRates

namespace CenteredCubeSqrt
open Filter CubeSqrtOverlap
open scoped Topology

theorem paperPairGeometryC_pos : 0<paperPairGeometryC := by unfold paperPairGeometryC; norm_num

noncomputable def paperPairPacketGap (T : ℝ) := retainedGap paperPairGeometryC T

theorem paper_pair_packet_gap_positive {T : ℝ} (hT : 1<T) : 0<paperPairPacketGap T := by
  unfold paperPairPacketGap retainedGap
  exact mul_pos (by have hc := paperPairGeometryC_pos; positivity) (Real.log_pos hT)

theorem paper_pair_packet_gap_ratio :
    Tendsto (fun T : ℝ => paperPairPacketGap T/T) atTop (𝓝 0) :=
  retained_gap_div_tendsto_zero paperPairGeometryC

theorem paper_pair_global_gap_tendsto {p : ℝ} (hp : 0<p) :
    Tendsto (fun m : ℕ =>
      paperPairGlobalEnvelope p ((m:ℝ)+paperPairPacketGap m) (paperPairPacketGap m) (m^3))
      atTop (𝓝 0) := by
  let c := paperPairGeometryC
  let F (m : ℕ) := paperPairGlobalEnvelope p ((m:ℝ)+paperPairPacketGap m) (paperPairPacketGap m) (m^3)
  let A := actualPairPrefactor*Real.exp (1/4)
  let D₀ := 4/(1-Real.exp (-c))
  let B := A*D₀*(paperCp p/18)
  have hc : 0<c := paperPairGeometryC_pos
  have hd : 0<1-Real.exp (-c) := sub_pos.mpr (Real.exp_lt_one_iff.2 (by linarith))
  have ha : 0≤A := by unfold A; exact mul_nonneg actual_pairPrefactor_nonneg (Real.exp_nonneg _)
  have hcp : 0<paperCp p := by unfold paperCp; positivity
  have hPow : Tendsto (fun m : ℕ => (m:ℝ)^3) atTop atTop :=
    (tendsto_pow_atTop (by decide : (3:ℕ)≠0)).comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hb : Tendsto (fun m : ℕ => B/(m:ℝ)^3) atTop (𝓝 0) := by
    simpa only [Function.comp_apply,div_eq_mul_inv,mul_zero] using
      (tendsto_inv_atTop_zero.comp hPow).const_mul B
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hb ?_ ?_
  · filter_upwards [eventually_gt_atTop (1:ℕ)] with m hm
    have hT : 1<(m:ℝ) := by exact_mod_cast hm
    have hpD := paper_pair_packet_gap_positive hT
    have hP : 0<(m:ℝ)+paperPairPacketGap m := by linarith
    have hDen : 0<1-Real.exp (-c*((m:ℝ)+paperPairPacketGap m)) :=
      sub_pos.mpr (Real.exp_lt_one_iff.2 (by nlinarith only [hc,hP]))
    have he : 0≤paperPairGeometricTerm ((m:ℝ)+paperPairPacketGap m) (paperPairPacketGap m) := by
      unfold paperPairGeometricTerm
      exact div_nonneg (mul_nonneg ha (Real.exp_nonneg _)) hDen.le
    unfold paperPairGlobalEnvelope
    positivity
  · filter_upwards [eventually_gt_atTop (1:ℕ)] with m hm
    let T := (m:ℝ)
    let P := T+paperPairPacketGap T
    have hT : 1<T := by dsimp [T]; exact_mod_cast hm
    have hT0 : 0<T := by linarith
    have hP : T≤P := by unfold P; linarith [paper_pair_packet_gap_positive hT]
    have hScale : paperCp p/(18*P)≤(paperCp p/18)/T := by
      rw [div_div]
      exact div_le_div_of_nonneg_left hcp.le (by positivity) (by linarith)
    have h := retained_gap_mesh_overlap_le (c:=c) hc hT.le
    change (T^3+1)^2*Real.exp (-c*paperPairPacketGap T)/
      (1-Real.exp (-c*P))≤D₀/T^2 at h
    have hB : 0≤A*(D₀/T^2) := mul_nonneg ha (by unfold D₀; positivity)
    calc
      F m = (A*((T^3+1)^2*Real.exp (-c*paperPairPacketGap T)/
        (1-Real.exp (-c*P))))*(paperCp p/(18*P)) := by
        unfold F paperPairGlobalEnvelope paperPairGeometricTerm A c T P
        push_cast
        ring
      _ ≤ (A*(D₀/T^2))*(paperCp p/(18*P)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h ha) (div_nonneg hcp.le (by linarith : 0≤18*P))
      _ ≤ (A*(D₀/T^2))*((paperCp p/18)/T) := mul_le_mul_of_nonneg_left hScale hB
      _ = B/(m:ℝ)^3 := by unfold B T; field_simp [show (m:ℝ)≠0 from by positivity] <;> ring

#print axioms paper_pair_global_gap_tendsto
end CenteredCubeSqrt
