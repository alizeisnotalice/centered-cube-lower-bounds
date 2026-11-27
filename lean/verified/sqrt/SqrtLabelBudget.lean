import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace CenteredCubeSqrt

/-- Exact per-condition union-cost threshold from papersidon. -/
noncomputable def labelBudget (B : ℝ) : ℝ :=
  let N := B-1
  let T := N*(N+1)/2
  let R := N*(N-1)
  N + T*(T-1) + 2*R^2 + 4*R

theorem labelBudget_lt_three (B : ℝ) (hB : 4 ≤ B) : labelBudget B < 3*B^4 := by
  let N := B-1
  let T := N*(N+1)/2
  let R := N*(N-1)
  have hB0 : 0 < B := by linarith
  have hN : 0 ≤ N := by dsimp [N]; linarith
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hR : 0 ≤ R := by
    exact mul_nonneg hN (by dsimp [N]; linarith)
  have hTN : T ≤ B^2/2 := by dsimp [T,N]; nlinarith
  have hRN : R ≤ B^2 := by dsimp [R,N]; nlinarith
  have hT2 := pow_le_pow_left₀ hT hTN 2
  have hR2 := pow_le_pow_left₀ hR hRN 2
  have hB2 : 16 ≤ B^2 := by nlinarith
  have hB4 : 64*B ≤ B^4 := by
    have := pow_le_pow_left₀ (show (0:ℝ) ≤ 4 by norm_num) hB 3
    nlinarith [mul_le_mul_of_nonneg_right this hB0.le]
  have hB3 : 16*B^2 ≤ B^4 := by
    nlinarith [mul_le_mul_of_nonneg_right hB2 (sq_nonneg B)]
  change N + T*(T-1) + 2*R^2 + 4*R < _
  dsimp [N] at *
  nlinarith

#print axioms labelBudget_lt_three

end CenteredCubeSqrt
