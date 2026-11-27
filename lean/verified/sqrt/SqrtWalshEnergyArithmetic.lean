import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace CenteredCubeSqrt

open scoped BigOperators

theorem sum_range_real_squares (n : ℕ) :
    (∑ j ∈ Finset.range n, (j:ℝ)^2) = ((n:ℝ)-1)*n*(2*n-1)/6 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ,ih,Nat.cast_succ]
    ring

/-- Exact piecewise-prefix energy from the paper, once the Walsh block shape
is established. This handles the half-step endpoints through zero contribution. -/
theorem walsh_block_energy_formula (B : ℝ) (hB : B ≠ 0) (q : ℕ) (hq : q ≠ 0) :
    B/(2*q)*((2*∑ j ∈ Finset.range q, (j:ℝ)^2 + (q:ℝ)^2)/B^3) =
      (q:ℝ)^2/(3*B^2) + 1/(6*B^2) := by
  have hq' : (q:ℝ) ≠ 0 := by exact_mod_cast hq
  rw [sum_range_real_squares]
  field_simp
  ring

#print axioms walsh_block_energy_formula

end CenteredCubeSqrt
