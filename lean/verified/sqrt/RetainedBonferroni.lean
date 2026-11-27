import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith

open Set MeasureTheory Finset
namespace CubeSqrtOverlap

/-- The exact second-order Bonferroni lower bound, with each unordered
retained packet pair counted only once. -/
theorem retained_bonferroni_real
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (R : Finset ℕ) (U : ℕ → Set Ω) (hm : ∀ i, MeasurableSet (U i)) :
    (∑ i ∈ R, μ.real (U i)) -
      (∑ i ∈ R, ∑ j ∈ R.filter (fun j ↦ i < j), μ.real (U i∩U j)) ≤
      μ.real (⋃ i ∈ R, U i) := by
  classical
  induction R using Finset.induction_on_min with
  | empty => simp
  | insert a S hmin ih =>
    have ha : a ∉ S := fun ha ↦ (lt_irrefl _) (hmin _ ha)
    have hUnion : (⋃ i ∈ insert a S, U i) = U a ∪ (⋃ i ∈ S, U i) := by
      ext w
      simp only [mem_iUnion,mem_union,Finset.mem_insert]
      constructor
      · rintro ⟨i,hi,h⟩
        rcases hi with rfl|hi
        · exact Or.inl h
        · exact Or.inr ⟨i,hi,h⟩
      · rintro (h|⟨i,hi,h⟩)
        · exact ⟨a,Or.inl rfl,h⟩
        · exact ⟨i,Or.inr hi,h⟩
    have hInt : μ.real (U a ∩ (⋃ i ∈ S,U i)) ≤ ∑ j ∈ S, μ.real (U a∩U j) := by
      simp only [inter_iUnion]
      exact measureReal_biUnion_finset_le S (fun j ↦ U a ∩ U j)
    have hNew : (insert a S).filter (fun j ↦ a < j) = S := by
      ext j
      simp only [mem_filter,Finset.mem_insert]
      constructor
      · rintro ⟨hj,hl⟩
        exact hj.resolve_left (fun h ↦ (lt_irrefl _) (h ▸ hl))
      · intro hj
        exact ⟨Or.inr hj,hmin _ hj⟩
    have hOld (i : ℕ) (hi : i ∈ S) :
        (insert a S).filter (fun j ↦ i < j) = S.filter (fun j ↦ i < j) := by
      ext j
      simp only [mem_filter,Finset.mem_insert]
      constructor
      · rintro ⟨hj,hl⟩
        exact ⟨hj.resolve_left (fun h ↦ (not_lt_of_ge (hmin _ hi).le) (h ▸ hl)),hl⟩
      · rintro ⟨hj,hl⟩
        exact ⟨Or.inr hj,hl⟩
    have hsum : (∑ i ∈ S, ∑ j ∈ (insert a S).filter (fun j ↦ i < j), μ.real (U i∩U j)) =
        ∑ i ∈ S, ∑ j ∈ S.filter (fun j ↦ i < j), μ.real (U i∩U j) :=
      sum_congr rfl fun i hi ↦ by rw [hOld i hi]
    rw [sum_insert ha,sum_insert ha,hNew,hsum,hUnion]
    have hExact := measureReal_union_add_inter' (μ:=μ) (t:=⋃ i ∈ S, U i) (hm a) (measure_ne_top _ _) (measure_ne_top _ _)
    linarith only [hInt,ih,hExact]

/-- A packet intersection is bounded by the sum of all its cross-node
intersections, with no independence assumption. -/
theorem packet_intersection_le_double_node_sum
    {Ω I : Type*} [MeasurableSpace Ω] [Fintype I] (μ : Measure Ω) [IsFiniteMeasure μ]
    (X Y : I → Set Ω) :
    μ.real ((⋃ i, X i)∩(⋃ j,Y j)) ≤ ∑ i, ∑ j, μ.real (X i∩Y j) := by
  rw [iUnion_inter]
  apply (measureReal_iUnion_fintype_le _).trans
  apply sum_le_sum
  intro i _
  rw [inter_iUnion]
  exact measureReal_iUnion_fintype_le _

end CubeSqrtOverlap
#print axioms CubeSqrtOverlap.retained_bonferroni_real
#print axioms CubeSqrtOverlap.packet_intersection_le_double_node_sum
