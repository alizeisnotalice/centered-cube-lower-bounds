import SqrtPlateauPolynomial
import Mathlib.NumberTheory.ZetaValues

namespace CenteredCubeSqrt

open Set
open scoped BigOperators
set_option maxHeartbeats 1800000

noncomputable def quarticB (x : ℝ) : ℝ := x^4-2*x^3+x^2+(bernoulli 4:ℚ)

theorem bernoulli_four_real_eval (x : ℝ) :
    (Polynomial.map (algebraMap ℚ ℝ) (Polynomial.bernoulli 4)).eval x = quarticB x := by
  have h3 : bernoulli 3 = 0 := bernoulli_eq_zero_of_odd (by decide) (by decide)
  rw [Polynomial.bernoulli_def]
  simp only [Polynomial.map_sum, Polynomial.eval_finsetSum]
  have hc : Nat.choose 4 2 = 6 := by decide
  norm_num [quarticB, Finset.sum_range_succ, bernoulli_zero, bernoulli_one, bernoulli_two,h3,hc]
  ring

noncomputable def cosineFourth (m : ℕ) (x : ℝ) : ℝ :=
  (1/(m:ℝ)^4)*Real.cos (2*Real.pi*(m:ℝ)*x)

theorem cosineFourth_hasSum {x : ℝ} (hx : x∈Icc (0:ℝ) 1) :
    HasSum (fun m : ℕ => cosineFourth m x) (-(Real.pi^4/3)*quarticB x) := by
  have hh := hasSum_one_div_nat_pow_mul_cos (k:=2) (by decide) hx
  rw [bernoulli_four_real_eval] at hh
  have e : -(Real.pi^4/3) = (-1 : ℝ)^(2+1)*(2*Real.pi)^(2*2)/2/(↑(2*2).factorial) := by
    norm_num
    ring
  rw [e]
  exact hh

theorem sine_four_square_expand (A X : ℝ) :
  16*(Real.sin A)^4*(Real.sin X)^2 =
    3 - 4*Real.cos (2*A) + Real.cos (2*(2*A)) - 3*Real.cos (2*X) +
      2*(Real.cos (2*A+2*X)+Real.cos (2*A-2*X)) -
      (Real.cos (2*(2*A)+2*X)+Real.cos (2*(2*A)-2*X))/2 := by
  rw [Real.cos_add (2*A),Real.cos_sub (2*A),Real.cos_add (2*(2*A)),Real.cos_sub (2*(2*A))]
  simp only [Real.cos_two_mul]
  have ha : Real.sin A^2 = 1-Real.cos A^2 := by linarith [Real.sin_sq_add_cos_sq A]
  have hx : Real.sin X^2 = 1-Real.cos X^2 := by linarith [Real.sin_sq_add_cos_sq X]
  rw [show (Real.sin A)^4=((Real.sin A)^2)^2 by ring,ha,hx]
  ring

#print axioms cosineFourth_hasSum
#print axioms sine_four_square_expand
end CenteredCubeSqrt
