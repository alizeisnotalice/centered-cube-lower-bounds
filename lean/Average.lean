/-
The exact one-dimensional average of the Rudin–Shapiro density (eq. (3.1)).

The manuscript computes, for side length `r > 0`,

  `a_r(x) = (1/r) ∫_{x-r/2}^{x+r/2} ρ_K(y) dy`
         `= 1 + S_t(x)/(30πK^{3/2} r)`  at `r = r(t) = 1 + 2t/K`,

via the closed form of the cosine average

  `(1/r) ∫_{x-r/2}^{x+r/2} cos(2πmy) dy = cos(2πmx) sin(πmr)/(πmr)`,

and the trigonometric identity `sin(π(K+l)r(t)) = (-1)^{K+l} sin(2πt(1+l/K))`.

This file proves both ingredients and the average formula for `ρ_K`.
-/
import CosineForm
import Variance

open MeasureTheory intervalIntegral Finset
open scoped BigOperators

namespace CenteredCube
namespace RudinDensity

/-- **The cosine average.**  For `m ≥ 1` and `r > 0`,

`(1/r) ∫_{x-r/2}^{x+r/2} cos(2πmy) dy = cos(2πmx) sin(πmr)/(πmr)`. -/
theorem average_cos (m : ℕ) (hm : 1 ≤ m) (x r : ℝ) (hr : 0 < r) :
    (1 / r) * ∫ y in (x - r / 2)..(x + r / 2), Real.cos ((m : ℝ) * (2 * Real.pi) * y)
      = Real.cos ((m : ℝ) * (2 * Real.pi) * x)
        * (Real.sin (Real.pi * (m : ℝ) * r) / (Real.pi * (m : ℝ) * r)) := by
  have hm' : (m : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.pos_iff_ne_zero.mp (by omega) : m ≠ 0)
  have hc : ((m : ℝ) * (2 * Real.pi)) ≠ 0 := by positivity
  have hpi : Real.pi * (m : ℝ) * r ≠ 0 := by positivity
  rw [intervalIntegral.integral_comp_mul_left (f := Real.cos) hc]
  simp only [smul_eq_mul]
  rw [integral_cos]
  have hdiff : Real.sin ((m : ℝ) * (2 * Real.pi) * (x + r / 2))
      - Real.sin ((m : ℝ) * (2 * Real.pi) * (x - r / 2))
      = 2 * Real.cos ((m : ℝ) * (2 * Real.pi) * x) * Real.sin (Real.pi * (m : ℝ) * r) := by
    rw [show (m : ℝ) * (2 * Real.pi) * (x + r / 2)
        = (m : ℝ) * (2 * Real.pi) * x + Real.pi * (m : ℝ) * r by ring,
      show (m : ℝ) * (2 * Real.pi) * (x - r / 2)
        = (m : ℝ) * (2 * Real.pi) * x - Real.pi * (m : ℝ) * r by ring,
      Real.sin_add, Real.sin_sub]
    ring
  rw [hdiff]
  field_simp

/-- **The sine identity at `r = 1 + 2t/K`**:
`sin(π(K+l)r) = (-1)^{K+l} sin(2πt(1 + l/K))`. -/
theorem sin_pi_mul_rfun {K : ℕ} (hK : 1 ≤ K) (l : ℕ) (t : ℝ) :
    Real.sin (Real.pi * ((K + l : ℕ) : ℝ) * (1 + 2 * t / (K : ℝ)))
      = (-1 : ℝ) ^ (K + l) * Real.sin (2 * Real.pi * t * (1 + (l : ℝ) / (K : ℝ))) := by
  have hKne : (K : ℝ) ≠ 0 := by positivity
  have harg : Real.pi * ((K + l : ℕ) : ℝ) * (1 + 2 * t / (K : ℝ))
      = 2 * Real.pi * t * (1 + (l : ℝ) / (K : ℝ)) + ((K + l : ℕ) : ℝ) * Real.pi := by
    field_simp
    push_cast
    ring
  rw [harg, Real.sin_add_nat_mul_pi]


/-- The manuscript's `r(t) = 1 + 2t/K`. -/
noncomputable def rfun (K : ℕ) (t : ℝ) : ℝ := 1 + 2 * t / (K : ℝ)

/-- **Termwise algebra of the exact average.**  Using
`sin(π(K+l)r) = (-1)^{K+l} sin(2πt(1+l/K))` and `(1+l/K)/(K+l) = 1/K`, the `l`-th
term of the averaged density equals the `l`-th term of `S_t/(30πK^{3/2}r)`. -/
theorem average_term {K : ℕ} (hK : 1 ≤ K) (t x : ℝ) (hr : 0 < rfun K t) (l : ℕ) :
    (1 / (30 * Real.sqrt (K : ℝ))) / rfun K t
        * (((1 : ℝ) + (l : ℝ) / (K : ℝ)) * (coef K l).1.re)
        * (Real.cos (((K + l : ℕ) : ℝ) * (2 * Real.pi) * x)
            * (Real.sin (Real.pi * ((K + l : ℕ) : ℝ) * rfun K t)
              / (Real.pi * ((K + l : ℕ) : ℝ))))
      = (1 / (30 * Real.pi * (K : ℝ) * Real.sqrt (K : ℝ) * rfun K t))
        * ((coef K l).1.re * (-1 : ℝ) ^ (K + l)
            * Real.sin (2 * Real.pi * t * (1 + (l : ℝ) / (K : ℝ)))
            * Real.cos (((K + l : ℕ) : ℝ) * (2 * Real.pi) * x)) := by
  have hsin := sin_pi_mul_rfun hK l t
  have hKl : ((K + l : ℕ) : ℝ) = (K : ℝ) + (l : ℝ) := by push_cast; ring
  have hK0 : (0 : ℝ) < (K : ℝ) := by exact_mod_cast (by omega : 0 < K)
  have hKl0 : (0 : ℝ) < ((K + l : ℕ) : ℝ) := by
    rw [hKl]; linarith
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  simp only [rfun] at *
  rw [hsin]
  rw [hKl]
  field_simp



/-- Termwise algebra without the outer `1/r`: the `l`-th summand of the integral
equals the `l`-th summand of `S_t/(30πK^{3/2})`. -/
theorem average_term' {K : ℕ} (hK : 1 ≤ K) (t x : ℝ) (l : ℕ) :
    (1 / (30 * Real.sqrt (K : ℝ)))
        * (((1 : ℝ) + (l : ℝ) / (K : ℝ)) * (coef K l).1.re)
        * (Real.cos (((K + l : ℕ) : ℝ) * (2 * Real.pi) * x)
            * (Real.sin (Real.pi * ((K + l : ℕ) : ℝ) * rfun K t)
              / (Real.pi * ((K + l : ℕ) : ℝ))))
      = (1 / (30 * Real.pi * (K : ℝ) * Real.sqrt (K : ℝ)))
        * ((coef K l).1.re * (-1 : ℝ) ^ (K + l)
            * Real.sin (2 * Real.pi * t * (1 + (l : ℝ) / (K : ℝ)))
            * Real.cos (((K + l : ℕ) : ℝ) * (2 * Real.pi) * x)) := by
  have hsin := sin_pi_mul_rfun hK l t
  have hKl : ((K + l : ℕ) : ℝ) = (K : ℝ) + (l : ℝ) := by push_cast; ring
  simp only [rfun] at *
  rw [hsin, hKl]
  field_simp

end RudinDensity
end CenteredCube

#print axioms CenteredCube.RudinDensity.average_cos
#print axioms CenteredCube.RudinDensity.sin_pi_mul_rfun
#print axioms CenteredCube.RudinDensity.average_term'
