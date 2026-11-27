/-
Trigonometric orthogonality on the period, for both manuscripts.

The `√n/log n` manuscript uses (eq. (3.2))

  `∫₀¹ cos(2πmx) cos(2πnx) dx = ½ δ_{mn}`,

to compute the mean and variance of the one-dimensional averages, and it uses
`∫₀¹ ρ_K = 1` for the normalisation of the density; the `√n` manuscript uses the
same orthogonality for the flat-variance condition.

This file proves the two elementary integrals everything else reduces to:
`∫₀¹ cos(2πkx) dx = 1` for `k = 0` and `0` otherwise, the same for `sin`, and
`∫₀¹ cos²(2πkx) dx = 1/2` for `k ≠ 0`.
-/
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

open MeasureTheory intervalIntegral
open scoped Real

namespace CenteredCube
namespace Trig

/-- `∫₀¹ cos(2πkx) dx` is `1` at `k = 0` and `0` for every other integer. -/
theorem integral_cos_two_pi_mul_int (k : ℤ) :
    ∫ x in (0 : ℝ)..1, Real.cos ((k : ℝ) * (2 * Real.pi) * x) = if k = 0 then 1 else 0 := by
  by_cases hk : k = 0
  · subst hk
    simp
  · rw [if_neg hk]
    have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk
    have hc : ((k : ℝ) * (2 * Real.pi)) ≠ 0 := by positivity
    rw [intervalIntegral.integral_comp_mul_left (f := Real.cos) hc]
    simp only [mul_zero, mul_one, smul_eq_mul]
    have hsin : Real.sin ((k : ℝ) * (2 * Real.pi)) = 0 := by
      rw [Real.sin_eq_zero_iff]
      exact ⟨2 * k, by push_cast; ring⟩
    rw [integral_cos, hsin, Real.sin_zero, sub_zero, mul_zero]

/-- `∫₀¹ sin(2πkx) dx = 0` for every integer `k`. -/
theorem integral_sin_two_pi_mul_int (k : ℤ) :
    ∫ x in (0 : ℝ)..1, Real.sin ((k : ℝ) * (2 * Real.pi) * x) = 0 := by
  by_cases hk : k = 0
  · subst hk
    simp
  · have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk
    have hc : ((k : ℝ) * (2 * Real.pi)) ≠ 0 := by positivity
    rw [intervalIntegral.integral_comp_mul_left (f := Real.sin) hc]
    simp only [mul_zero, mul_one, smul_eq_mul]
    rw [integral_sin, Real.cos_int_mul_two_pi, Real.cos_zero, sub_self, mul_zero]

/-- `∫₀¹ cos²(2πkx) dx = 1/2` for `k ≠ 0`, the diagonal case of the orthogonality
relation used for the variance identities. -/
theorem integral_cos_sq_two_pi_mul_int (k : ℤ) (hk : k ≠ 0) :
    ∫ x in (0 : ℝ)..1, Real.cos ((k : ℝ) * (2 * Real.pi) * x) ^ 2 = 1 / 2 := by
  have hpt : ∀ x : ℝ,
      Real.cos ((k : ℝ) * (2 * Real.pi) * x) ^ 2
        = 1 / 2 + Real.cos (((2 * k : ℤ) : ℝ) * (2 * Real.pi) * x) / 2 := by
    intro x
    have h := Real.cos_two_mul ((k : ℝ) * (2 * Real.pi) * x)
    have harg : 2 * ((k : ℝ) * (2 * Real.pi) * x)
        = ((2 * k : ℤ) : ℝ) * (2 * Real.pi) * x := by
      push_cast
      ring
    rw [harg] at h
    linarith
  simp only [hpt]
  have hcont : Continuous fun x : ℝ => Real.cos (((2 * k : ℤ) : ℝ) * (2 * Real.pi) * x) := by
    fun_prop
  have hsplit : ∫ x in (0 : ℝ)..1,
        (1 / 2 + Real.cos (((2 * k : ℤ) : ℝ) * (2 * Real.pi) * x) / 2)
      = (∫ x in (0 : ℝ)..1, (1 / 2 : ℝ))
        + ∫ x in (0 : ℝ)..1, Real.cos (((2 * k : ℤ) : ℝ) * (2 * Real.pi) * x) / 2 :=
    intervalIntegral.integral_add intervalIntegrable_const
      ((hcont.div_const 2).intervalIntegrable 0 1)
  rw [hsplit]
  have hne : (2 * k : ℤ) ≠ 0 := by omega
  simp only [intervalIntegral.integral_const, intervalIntegral.integral_div,
    integral_cos_two_pi_mul_int (2 * k), if_neg hne, sub_zero, smul_eq_mul]
  norm_num


/-- `2 cos A cos B = cos (A - B) + cos (A + B)`. -/
theorem two_mul_cos_mul_cos (A B : ℝ) :
    2 * (Real.cos A * Real.cos B) = Real.cos (A - B) + Real.cos (A + B) := by
  have h1 := Real.cos_add A B
  have h2 := Real.cos_sub A B
  linarith

/-- **The orthogonality relation of eq. (3.2).**  For positive integers `m, n`,
`∫₀¹ cos(2πmx) cos(2πnx) dx = ½` if `m = n` and `0` otherwise. -/
theorem integral_cos_mul_cos_two_pi {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    ∫ x in (0 : ℝ)..1,
        Real.cos ((m : ℝ) * (2 * Real.pi) * x) * Real.cos ((n : ℝ) * (2 * Real.pi) * x)
      = if m = n then 1 / 2 else 0 := by
  have hpt : ∀ x : ℝ,
      Real.cos ((m : ℝ) * (2 * Real.pi) * x) * Real.cos ((n : ℝ) * (2 * Real.pi) * x)
        = 1 / 2 * Real.cos ((((m : ℤ) - n : ℤ) : ℝ) * (2 * Real.pi) * x)
          + 1 / 2 * Real.cos ((((m : ℤ) + n : ℤ) : ℝ) * (2 * Real.pi) * x) := by
    intro x
    have h := two_mul_cos_mul_cos ((m : ℝ) * (2 * Real.pi) * x) ((n : ℝ) * (2 * Real.pi) * x)
    have harg1 : ((m : ℝ) * (2 * Real.pi) * x - (n : ℝ) * (2 * Real.pi) * x)
        = (((m : ℤ) - n : ℤ) : ℝ) * (2 * Real.pi) * x := by push_cast; ring
    have harg2 : ((m : ℝ) * (2 * Real.pi) * x + (n : ℝ) * (2 * Real.pi) * x)
        = (((m : ℤ) + n : ℤ) : ℝ) * (2 * Real.pi) * x := by push_cast; ring
    rw [harg1, harg2] at h
    linarith
  simp only [hpt]
  have hcont1 : Continuous fun x : ℝ => Real.cos ((((m : ℤ) - n : ℤ) : ℝ) * (2 * Real.pi) * x) := by
    fun_prop
  have hcont2 : Continuous fun x : ℝ => Real.cos ((((m : ℤ) + n : ℤ) : ℝ) * (2 * Real.pi) * x) := by
    fun_prop
  have hsplit : ∫ x in (0 : ℝ)..1,
        (1 / 2 * Real.cos ((((m : ℤ) - n : ℤ) : ℝ) * (2 * Real.pi) * x)
          + 1 / 2 * Real.cos ((((m : ℤ) + n : ℤ) : ℝ) * (2 * Real.pi) * x))
      = (∫ x in (0 : ℝ)..1, 1 / 2 * Real.cos ((((m : ℤ) - n : ℤ) : ℝ) * (2 * Real.pi) * x))
        + ∫ x in (0 : ℝ)..1, 1 / 2 * Real.cos ((((m : ℤ) + n : ℤ) : ℝ) * (2 * Real.pi) * x) :=
    intervalIntegral.integral_add ((hcont1.const_mul (1/2)).intervalIntegrable 0 1)
      ((hcont2.const_mul (1/2)).intervalIntegrable 0 1)
  rw [hsplit]
  have h1 : ∫ x in (0 : ℝ)..1, 1 / 2 * Real.cos ((((m : ℤ) - n : ℤ) : ℝ) * (2 * Real.pi) * x)
      = 1 / 2 * (if (m : ℤ) - n = 0 then 1 else 0) := by
    rw [intervalIntegral.integral_const_mul, integral_cos_two_pi_mul_int ((m : ℤ) - n)]
  have h2 : ∫ x in (0 : ℝ)..1, 1 / 2 * Real.cos ((((m : ℤ) + n : ℤ) : ℝ) * (2 * Real.pi) * x)
      = 1 / 2 * (if (m : ℤ) + n = 0 then 1 else 0) := by
    rw [intervalIntegral.integral_const_mul, integral_cos_two_pi_mul_int ((m : ℤ) + n)]
  rw [h1, h2]
  have hsum : ((m : ℤ) + n) ≠ 0 := by
    have : (0 : ℤ) < m := by exact_mod_cast hm
    have : (0 : ℤ) < n := by exact_mod_cast hn
    omega
  rw [if_neg hsum]
  by_cases hmn : m = n
  · subst hmn
    rw [if_pos rfl]
    rw [show ((m : ℤ) - m) = 0 by ring, if_pos rfl]
    norm_num
  · rw [if_neg hmn]
    have hd : ((m : ℤ) - n) ≠ 0 := by
      intro h
      apply hmn
      omega
    rw [if_neg hd]
    norm_num

end Trig
end CenteredCube

#print axioms CenteredCube.Trig.integral_cos_two_pi_mul_int
#print axioms CenteredCube.Trig.integral_sin_two_pi_mul_int
#print axioms CenteredCube.Trig.integral_cos_sq_two_pi_mul_int
#print axioms CenteredCube.Trig.integral_cos_mul_cos_two_pi
