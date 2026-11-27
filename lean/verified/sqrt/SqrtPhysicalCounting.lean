import SqrtPhysicalCountingCore
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open scoped BigOperators

namespace CenteredCubeSqrt

theorem sumLabels_eq_finset (f : ℕ → ℕ) (n : ℕ) :
    sumLabels f n = ∑ x ∈ Finset.range n, f x := by
  induction n with
  | zero => simp [sumLabels]
  | succ n ih => rw [sumLabels, ih, Finset.sum_range_succ]

/-- Finset version of the exact regular two-carry count. -/
theorem physical_count_from_regular_fibers {q B b A : ℕ}
    (hb : b < B) (hA : q = B * B * A)
    (N0 N1 : ℕ → ℕ)
    (h0 : ∀ y ∈ Finset.range (B-b), N0 y = A - if y = 0 ∧ b = 0 then 1 else 0)
    (h1 : ∀ y ∈ Finset.range b, N1 y = A)
    (hp : 0 < A) :
    (∑ y ∈ Finset.range (B-b), N0 y) + (∑ y ∈ Finset.range b, N1 y) =
      q/B - if b = 0 then 1 else 0 := by
  rw [← sumLabels_eq_finset, ← sumLabels_eq_finset]
  exact regular_physical_count_core hb hA hp N0 N1
    (fun y hy => h0 y (Finset.mem_range.mpr hy))
    (fun y hy => h1 y (Finset.mem_range.mpr hy))

theorem physical_count_small_positive {b A : ℕ} (N : ℕ → ℕ)
    (h : ∀ i ∈ Finset.range b, N i = A) :
    (∑ i ∈ Finset.range b, N i) = A*b := by
  rw [← sumLabels_eq_finset, Nat.mul_comm A b]
  exact small_positive_physical_count_core N (fun y hy => h y (Finset.mem_range.mpr hy))

#print axioms physical_count_from_regular_fibers
#print axioms physical_count_small_positive

end CenteredCubeSqrt
