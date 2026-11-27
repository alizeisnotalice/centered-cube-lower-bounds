import RetainedCountLimit
import ActualDeletionBands

open Set Finset
namespace CubeSqrtOverlap

noncomputable def paperPacketLength (K v P A : ℝ) (i a : ℕ) : ℝ :=
  10/9+2*((i:ℝ)*P+(a:ℝ)*A)/(K*v)

theorem paper_packet_raw_grid_valid
    (K v P A : ℝ) (hK : 0 < K) (hv : 0 < v) (hP : 0 < P) (hA : 0 ≤ A)
    (N : ℕ) (hV : (N:ℝ)*A ≤ K*v/18)
    (i : ℕ) (hi : i ∈ range (rawPacketCount (K*v/18) ((N:ℝ)*A) P))
    (a : Fin (N+1)) :
    paperPacketLength K v P A i a.1 ∈ Set.Icc (10/9:ℝ) (11/9:ℝ) := by
  have hEnd := (raw_packet_mem_range_iff (K*v/18) ((N:ℝ)*A) P hP hV i).mp hi
  have ha : (a.1:ℝ) ≤ (N:ℝ) := by exact_mod_cast (show a.1 ≤ N by omega)
  have hL : 0 ≤ (i:ℝ)*P+(a.1:ℝ)*A := by positivity
  have hM := mul_le_mul_of_nonneg_right ha hA
  have hU : (i:ℝ)*P+(a.1:ℝ)*A ≤ K*v/18 := by linarith only [hEnd,hM]
  have hp := mul_pos hK hv
  have hL' : 0 ≤ 2*((i:ℝ)*P+(a.1:ℝ)*A)/(K*v) := div_nonneg (mul_nonneg (by norm_num) hL) hp.le
  have hU' : 2*((i:ℝ)*P+(a.1:ℝ)*A)/(K*v) ≤ 1/9 := by
    apply (div_le_iff₀ hp).2
    linarith only [hU]
  unfold paperPacketLength
  exact ⟨by linarith only [hL'],by linarith only [hU']⟩

theorem paper_packet_node_gap
    (K v P A : ℝ) (hK : 0 < K) (hv : 0 < v)
    (i j a b : ℕ) :
    K*v/2*(paperPacketLength K v P A j b-paperPacketLength K v P A i a) =
      ((j:ℝ)-(i:ℝ))*P+((b:ℝ)-(a:ℝ))*A := by
  unfold paperPacketLength
  field_simp [hK.ne',hv.ne'] <;> ring

/-- Applied to the real source, the safe-deletion bound needs only that each
unsafe node lies within the manuscript radius of some periodic defect. -/
theorem paper_unsafe_packet_deletion_budget
    {J : Type*} [Fintype J] (defect : J → ℝ)
    (K v P A : ℝ) (hK : 5 ≤ K) (hv : 0 < v) (hP : 0 < P) (hA : 0 ≤ A)
    (N : ℕ) (hV : (N:ℝ)*A ≤ K*v/18)
    (deleted : Finset ℕ)
    (hR : deleted ⊆ range (rawPacketCount (K*v/18) ((N:ℝ)*A) P))
    (hBad : ∀ i ∈ deleted, ∃ (a : Fin (N+1)) (j : J) (m : ℤ),
      |K*(paperPacketLength K v P A i a.1-1)-(defect j+(m:ℝ)*K)| ≤ 2) :
    (deleted.card:ℝ) ≤ ((N:ℝ)+1)*(Fintype.card J:ℝ)*(2*v/P+1) := by
  have hK0 : 0 < K := by linarith only [hK]
  let Δ := 2*P/(K*v)
  let b (a : Fin (N+1)) := 10/9+2*(a.1:ℝ)*A/(K*v)
  have hEq (i : ℕ) (a : Fin (N+1)) :
      b a+(i:ℝ)*Δ = paperPacketLength K v P A i a.1 := by
    unfold b Δ paperPacketLength
    ring
  have hPhysical (i : ℕ) (hi : i ∈ range (rawPacketCount (K*v/18) ((N:ℝ)*A) P)) (a : Fin (N+1)) :
      K*(b a+(i:ℝ)*Δ-1) ∈ Set.Icc (K/9) (2*K/9) := by
    rw [hEq]
    have h := paper_packet_raw_grid_valid K v P A hK0 hv hP hA N hV i hi a
    have hL := mul_le_mul_of_nonneg_left h.1 hK0.le
    have hU := mul_le_mul_of_nonneg_left h.2 hK0.le
    exact ⟨by nlinarith only [hL],by nlinarith only [hU]⟩
  have hBad' : ∀ i ∈ deleted, ∃ (a : Fin (N+1)) (j : J) (m : ℤ),
      |K*(b a+(i:ℝ)*Δ-1)-(defect j+(m:ℝ)*K)| ≤ 2 := by
    intro i hi
    obtain ⟨a,j,m,hh⟩ := hBad i hi
    exact ⟨a,j,m,by simpa only [hEq] using hh⟩
  have h := actual_unsafe_packet_deletions _ deleted hR b defect K Δ hK (by dsimp [Δ]; positivity)
    hPhysical hBad'
  have hRate : (4/K)/Δ = 2*v/P := by unfold Δ; field_simp [hK0.ne',hv.ne',hP.ne'] <;> ring
  simpa only [Fintype.card_fin,Nat.cast_add,Nat.cast_one,hRate] using h

end CubeSqrtOverlap
#print axioms CubeSqrtOverlap.paper_packet_node_gap
#print axioms CubeSqrtOverlap.paper_unsafe_packet_deletion_budget
