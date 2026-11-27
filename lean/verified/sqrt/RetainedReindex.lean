import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Linarith

open Finset
namespace CubeSqrtOverlap

/-- A row of original retained pairs can be reindexed by the true original
gap, retaining zeroes for missing packets. -/
theorem retained_row_as_original_gaps
    (B : ℕ) (R : Finset ℕ) (hR : R ⊆ range B) (i : ℕ) (F : ℕ → ℝ) :
    (∑ j ∈ R.filter (fun j ↦ i < j), F j) =
      ∑ k ∈ range (B-i-1), if i+k+1 ∈ R then F (i+k+1) else 0 := by
  classical
  let U := (range B).filter fun j ↦ i < j
  have hSub : R.filter (fun j ↦ i < j) ⊆ U := by
    intro j hj
    exact mem_filter.mpr ⟨hR (mem_filter.mp hj).1,(mem_filter.mp hj).2⟩
  let G (j : ℕ) := if j ∈ R then F j else 0
  have hG₁ : (∑ j ∈ R.filter (fun j ↦ i < j), F j) =
      ∑ j ∈ R.filter (fun j ↦ i < j), G j := by
    apply sum_congr rfl
    intro j hj
    simp [G,(mem_filter.mp hj).1]
  have hG₂ : (∑ j ∈ R.filter (fun j ↦ i < j), G j) = ∑ j ∈ U, G j := by
    apply sum_subset hSub
    intro j hj hj'
    have hji : i < j := (mem_filter.mp hj).2
    have hn : j ∉ R := fun h ↦ hj' (mem_filter.mpr ⟨h,hji⟩)
    simp [G,hn]
  rw [hG₁,hG₂]
  symm
  change (∑ k ∈ range (B-i-1), G (i+k+1)) = ∑ j ∈ U, G j
  refine sum_bij' (fun k _ ↦ i+k+1) (fun j _ ↦ j-i-1) ?_ ?_ ?_ ?_ ?_
  · intro k hk
    have hkr := mem_range.mp hk
    exact mem_filter.mpr ⟨mem_range.mpr (by omega),by omega⟩
  · intro j hj
    have hjr := mem_range.mp (mem_filter.mp hj).1
    have hij := (mem_filter.mp hj).2
    exact mem_range.mpr (by omega)
  · intro k hk
    omega
  · intro j hj
    have hij := (mem_filter.mp hj).2
    omega
  · simp

theorem retained_far_total
    {I J : Type*} [Fintype I] [Fintype J] (B : ℕ) (R : Finset ℕ) (C : ℝ) (hC : 0 ≤ C)
    (W : ℕ → ℕ → I → J → ℝ)
    (hW : ∀ i ∈ R, ∀ k ∈ range (B-i-1), ∀ l j, W i k l j ≤ C) :
    (∑ i ∈ R, ∑ k ∈ range (B-i-1), ∑ l : I, ∑ j : J, W i k l j) ≤
      (R.card:ℝ)*(B:ℝ)*(Fintype.card I:ℝ)*(Fintype.card J:ℝ)*C := by
  let A := (Fintype.card I:ℝ)*(Fintype.card J:ℝ)*C
  have hA : 0 ≤ A := mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hC
  have hRow (i : ℕ) (hi : i ∈ R) :
      (∑ k ∈ range (B-i-1), ∑ l : I, ∑ j : J, W i k l j) ≤ (B:ℝ)*A := by
    calc
      _ ≤ ∑ _k ∈ range (B-i-1), ∑ _l : I, ∑ _j : J, C :=
        sum_le_sum fun k hk ↦ sum_le_sum fun l _ ↦ sum_le_sum fun j _ ↦ hW i hi k hk l j
      _ = ((B-i-1:ℕ):ℝ)*A := by simp [A,mul_assoc]
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast (show B-i-1≤B by omega)) hA
  calc
    _ ≤ ∑ _i ∈ R, (B:ℝ)*A := sum_le_sum fun i hi ↦ hRow i hi
    _ = _ := by simp [A,mul_assoc]

end CubeSqrtOverlap
#print axioms CubeSqrtOverlap.retained_row_as_original_gaps
#print axioms CubeSqrtOverlap.retained_far_total
