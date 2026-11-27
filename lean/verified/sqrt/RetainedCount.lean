import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Finset.Max
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push

open Set Finset
namespace CubeSqrtOverlap

theorem spacing_grid_band_card (S : Finset ℕ) (b δ low high : ℝ)
    (hδ : 0 < δ) (hWidth : low ≤ high)
    (hS : ∀ i ∈ S, b+(i:ℝ)*δ ∈ Set.Icc low high) :
    (S.card:ℝ) ≤ (high-low)/δ+1 := by
  by_cases hne : S.Nonempty
  · let l := S.min' hne
    let h := S.max' hne
    have hL := hS l (S.min'_mem hne)
    have hH := hS h (S.max'_mem hne)
    have hSub : S ⊆ Finset.Icc l h := by
      intro i hi
      exact Finset.mem_Icc.mpr ⟨S.min'_le i hi,S.le_max' i hi⟩
    have hlh : l ≤ h := S.min'_le h (S.max'_mem hne)
    have hC : S.card ≤ (Finset.Icc l h).card := Finset.card_le_card hSub
    rw [Nat.card_Icc] at hC
    have hC' : (S.card:ℝ) ≤ (h:ℝ)+1-(l:ℝ) := by
      have h := Nat.cast_le (α:=ℝ).2 hC
      rwa [Nat.cast_sub (by omega),Nat.cast_add,Nat.cast_one] at h
    have hD' : ((h:ℝ)-(l:ℝ))*δ ≤ high-low := by
      linarith only [hL.1,hH.2]
    have hD := (le_div_iff₀ hδ).2 hD'
    linarith only [hC',hD]
  · have hE : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    rw [hE,Finset.card_empty,Nat.cast_zero]
    have hn : 0 ≤ (high-low)/δ := div_nonneg (sub_nonneg.mpr hWidth) hδ.le
    linarith only [hn]

/-- There are exactly floor((V−T)/P)+1 raw packets with the final
node at or below the outer endpoint. -/
theorem raw_packet_mem_range_iff (V T P : ℝ) (hP : 0 < P) (hV : T ≤ V) (i : ℕ) :
    i ∈ range (⌊(V-T)/P⌋₊+1) ↔ (i:ℝ)*P+T ≤ V := by
  have hQ : 0 ≤ (V-T)/P := div_nonneg (sub_nonneg.mpr hV) hP.le
  rw [Finset.mem_range,Nat.lt_succ_iff,Nat.le_floor_iff hQ,le_div_iff₀ hP]
  constructor <;> intro h <;> linarith only [h]

theorem raw_packet_count_error (V T P : ℝ) (hP : 0 < P) (hT : 0 ≤ T) (hV : T ≤ V) :
    |((⌊(V-T)/P⌋₊+1:ℕ):ℝ)-V/P| ≤ T/P+1 := by
  let q := (V-T)/P
  have hQ : 0 ≤ q := div_nonneg (sub_nonneg.mpr hV) hP.le
  have he : V/P-T/P = q := (sub_div V T P).symm
  have hL : V/P-T/P < (⌊q⌋₊:ℝ)+1 := by rw [he]; exact Nat.lt_floor_add_one q
  have hU : (⌊q⌋₊:ℝ) ≤ V/P-T/P := by rw [he]; exact Nat.floor_le hQ
  change |((⌊q⌋₊+1:ℕ):ℝ)-V/P| ≤ T/P+1
  push_cast
  apply abs_le.mpr
  have hTP := div_nonneg hT hP.le
  exact ⟨by linarith only [hL],by linarith only [hU,hTP]⟩

/-- Every deleted index is covered by at least one node/defect band.
Counting a multiply-hit index several times can only increase the upper bound. -/
theorem packet_deletions_le
    {I J : Type*} [Fintype I] [Fintype J]
    (deleted : Finset ℕ) (bad : I → J → Finset ℕ) (C : ℝ)
    (hcover : ∀ n ∈ deleted, ∃ i j, n ∈ bad i j)
    (hbad : ∀ i j, ((bad i j).card:ℝ) ≤ C) :
    (deleted.card:ℝ) ≤ (Fintype.card I:ℝ)*(Fintype.card J:ℝ)*C := by
  classical
  let U := (univ : Finset I).biUnion (fun i ↦ (univ : Finset J).biUnion (bad i))
  have hS : deleted ⊆ U := by
    intro n hn
    obtain ⟨i,j,h⟩ := hcover n hn
    exact mem_biUnion.mpr ⟨i,mem_univ _,mem_biUnion.mpr ⟨j,mem_univ _,h⟩⟩
  have hSum : U.card ≤ ∑ i : I, ∑ j : J, (bad i j).card :=
    card_biUnion_le.trans (sum_le_sum fun i _ ↦ card_biUnion_le)
  calc
    _ ≤ (((∑ i : I, ∑ j : J, (bad i j).card):ℕ):ℝ) := by exact_mod_cast (Finset.card_le_card hS).trans hSum
    _ ≤ ∑ _i : I, ∑ _j : J, C := by
      simp only [Nat.cast_sum]
      exact sum_le_sum fun i _ ↦ sum_le_sum fun j _ ↦ hbad i j
    _ = _ := by simp [mul_assoc]

end CubeSqrtOverlap
#print axioms CubeSqrtOverlap.spacing_grid_band_card
#print axioms CubeSqrtOverlap.raw_packet_count_error
#print axioms CubeSqrtOverlap.packet_deletions_le
