import PaperPacketGeometry
import RetainedNear

open Set Finset
namespace CubeSqrtOverlap

/-- Original-gap coordinates of distinct retained packets: every cross-node
difference is positive and belongs to the actual kernel proof's horizon. -/
theorem paper_packet_tau_domain
    (K v P A D : ℝ) (hK : 0 < K) (hv : 0 < v) (hP : 0 < P)
    (hA : 0 ≤ A) (hD : 0 < D) (N : ℕ)
    (hP₀ : (N:ℝ)*A+D ≤ P) (hV : (N:ℝ)*A ≤ K*v/18)
    (i j : ℕ) (hi : i ∈ range (rawPacketCount (K*v/18) ((N:ℝ)*A) P))
    (hj : j ∈ range (rawPacketCount (K*v/18) ((N:ℝ)*A) P)) (hij : i < j)
    (a b : Fin (N+1)) :
    let r := ((j:ℝ)-(i:ℝ))*P+((b.1:ℝ)-(a.1:ℝ))*A
    let τ := K*(paperPacketLength K v P A j b.1-paperPacketLength K v P A i a.1)/2
    τ = r/v ∧ 0 < τ ∧ τ ≤ K/18 := by
  dsimp only
  let r := ((j:ℝ)-(i:ℝ))*P+((b.1:ℝ)-(a.1:ℝ))*A
  let R := paperPacketLength K v P A j b.1-paperPacketLength K v P A i a.1
  have hGap := paper_packet_node_gap K v P A hK hv i j a.1 b.1
  have hEq : K*R/2 = r/v := by
    apply (eq_div_iff hv.ne').2
    change (K*R/2)*v = r
    change K*v/2*R = r at hGap
    linear_combination hGap
  have hA0 : 0 ≤ (a.1:ℝ)*A := by positivity
  have hB0 : 0 ≤ (b.1:ℝ)*A := by positivity
  have haN : (a.1:ℝ) ≤ (N:ℝ) := by exact_mod_cast (show a.1 ≤ N by omega)
  have haU := mul_le_mul_of_nonneg_right haN hA
  let k := j-i-1
  have hj' : j = i+k+1 := by unfold k; omega
  have hB : D+(k:ℝ)*P ≤ r := by
    have h := retained_node_distance hP₀ hP.le hA0 haU hB0 i k
    rw [←hj'] at h
    dsimp [r]
    convert h using 1 <;> ring
  have hr : 0 < r := (add_pos_of_pos_of_nonneg hD (by positivity : 0 ≤ (k:ℝ)*P)).trans_le hB
  have hiI := paper_packet_raw_grid_valid K v P A hK hv hP hA N hV i hi a
  have hjI := paper_packet_raw_grid_valid K v P A hK hv hP hA N hV j hj b
  have hGapU : R ≤ 1/9 := by
    unfold R
    linarith only [hiI.1,hjI.2]
  have hU := mul_le_mul_of_nonneg_left hGapU hK.le
  refine ⟨hEq,?_,?_⟩
  · rw [hEq]; exact div_pos hr hv
  · change K*R/2 ≤ K/18
    linarith only [hU]

end CubeSqrtOverlap
#print axioms CubeSqrtOverlap.paper_packet_tau_domain
