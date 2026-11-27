/-
The exact one-dimensional average of the Rudin–Shapiro density (eq. (3.1)).

The manuscript computes, for side length `r > 0`,

  `a_r(x) = (1/r) ∫_{x-r/2}^{x+r/2} ρ_K(y) dy`
         `= 1 + S_t(x)/(30πK^{3/2} r)`  at `r = r(t) = 1 + 2t/K`,

via the closed form of the cosine average

  `(1/r) ∫_{x-r/2}^{x+r/2} cos(2πmy) dy = cos(2πmx) sin(πmr)/(πmr)`,

and the trigonometric identity `sin(π(K+l)r(t)) = (-1)^{K+l} sin(2πt(1+l/K))`.

This file proves both ingredients, the termwise algebra, and the assembled
identity in integral form `∫ ρ_K = r(t) + S_t/(30πK^{3/2})`.
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

/-- **The cosine integral with the length cancelled.**  Because `average_cos` carries
`sin(πmr)/(πmr)`, the factor `r` cancels against the outer `1/r` of the *average*, so
the raw integral has no `r` in the denominator:

`∫_{x-r/2}^{x+r/2} cos(2πmy) dy = cos(2πmx)·sin(πmr)/(πm)`. -/
theorem integral_cos_shift (m : ℕ) (hm : 1 ≤ m) (x r : ℝ) (hr : 0 < r) :
    ∫ y in (x - r / 2)..(x + r / 2), Real.cos ((m : ℝ) * (2 * Real.pi) * y)
      = Real.cos ((m : ℝ) * (2 * Real.pi) * x)
          * (Real.sin (Real.pi * (m : ℝ) * r) / (Real.pi * (m : ℝ))) := by
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hrne : r ≠ 0 := hr.ne'
  have hI : (∫ y in (x - r / 2)..(x + r / 2), Real.cos ((m : ℝ) * (2 * Real.pi) * y))
      = r * ((1 / r) * ∫ y in (x - r / 2)..(x + r / 2),
          Real.cos ((m : ℝ) * (2 * Real.pi) * y)) := by
    field_simp
  rw [hI, average_cos m hm x r hr]
  field_simp

/-- The same, termwise for a finite cosine series. -/
theorem integral_cos_sum_shift {K M : ℕ} (hM : 0 < M) (a : ℕ → ℝ) (x r : ℝ)
    (hr : 0 < r) :
    ∫ y in (x - r / 2)..(x + r / 2),
        ∑ l ∈ range K, a l * Real.cos (((M + l : ℕ) : ℝ) * (2 * Real.pi) * y)
      = ∑ l ∈ range K, a l * (Real.cos (((M + l : ℕ) : ℝ) * (2 * Real.pi) * x)
          * (Real.sin (Real.pi * ((M + l : ℕ) : ℝ) * r)
            / (Real.pi * ((M + l : ℕ) : ℝ)))) := by
  have hcont : ∀ l : ℕ, Continuous fun y : ℝ =>
      a l * Real.cos (((M + l : ℕ) : ℝ) * (2 * Real.pi) * y) := by
    intro l
    fun_prop
  rw [intervalIntegral.integral_finsetSum (fun l _ => (hcont l).intervalIntegrable _ _)]
  exact Finset.sum_congr rfl (fun l _ => by
    rw [intervalIntegral.integral_const_mul, integral_cos_shift (M + l) (by omega) x r hr])

/-- **The exact one-dimensional average, integral form (eq. (3.1)).**

At `r = r(t) = 1 + 2t/K`,

`∫_{x-r/2}^{x+r/2} ρ_K(y) dy = r + S_t(x)/(30πK^{3/2})`,

so dividing by `r` gives the manuscript's `(1/r)∫ρ_K = 1 + S_t/(30πK^{3/2}r)`. -/
theorem integral_rho_shift {K : ℕ} (hK : 1 ≤ K) (t x : ℝ) (hr : 0 < rfun K t) :
    ∫ y in (x - rfun K t / 2)..(x + rfun K t / 2), rho K y
      = rfun K t + Sfun K t x / (30 * Real.pi * (K : ℝ) * Real.sqrt (K : ℝ)) := by
  have hpt : ∀ y : ℝ, rho K y = 1 + (1 / (30 * Real.sqrt (K : ℝ))) * ∑ l ∈ range K,
      (((1 : ℝ) + (l : ℝ) / (K : ℝ)) * (coef K l).1.re)
        * Real.cos (((K + l : ℕ) : ℝ) * (2 * Real.pi) * y) :=
    fun y => rho_eq_cos_series hK y
  have hcont : ∀ l : ℕ, Continuous fun y : ℝ =>
      (((1 : ℝ) + (l : ℝ) / (K : ℝ)) * (coef K l).1.re)
        * Real.cos (((K + l : ℕ) : ℝ) * (2 * Real.pi) * y) := by
    intro l
    fun_prop
  have hsumcont : Continuous fun y : ℝ => ∑ l ∈ range K,
      (((1 : ℝ) + (l : ℝ) / (K : ℝ)) * (coef K l).1.re)
        * Real.cos (((K + l : ℕ) : ℝ) * (2 * Real.pi) * y) :=
    continuous_finset_sum_interval _ (fun l _ => hcont l)
  have hsum : ∫ y in (x - rfun K t / 2)..(x + rfun K t / 2),
        (∑ l ∈ range K, (((1 : ℝ) + (l : ℝ) / (K : ℝ)) * (coef K l).1.re)
          * Real.cos (((K + l : ℕ) : ℝ) * (2 * Real.pi) * y))
      = ∑ l ∈ range K, (((1 : ℝ) + (l : ℝ) / (K : ℝ)) * (coef K l).1.re)
          * (Real.cos (((K + l : ℕ) : ℝ) * (2 * Real.pi) * x)
            * (Real.sin (Real.pi * ((K + l : ℕ) : ℝ) * rfun K t)
              / (Real.pi * ((K + l : ℕ) : ℝ)))) :=
    integral_cos_sum_shift (K := K) (M := K) (by omega) _ x (rfun K t) hr
  have hInt : ∫ y in (x - rfun K t / 2)..(x + rfun K t / 2), rho K y
      = rfun K t + (1 / (30 * Real.sqrt (K : ℝ))) * ∑ l ∈ range K,
          (((1 : ℝ) + (l : ℝ) / (K : ℝ)) * (coef K l).1.re)
            * (Real.cos (((K + l : ℕ) : ℝ) * (2 * Real.pi) * x)
              * (Real.sin (Real.pi * ((K + l : ℕ) : ℝ) * rfun K t)
                / (Real.pi * ((K + l : ℕ) : ℝ)))) := by
    have h1 : ∫ y in (x - rfun K t / 2)..(x + rfun K t / 2), rho K y
        = ∫ y in (x - rfun K t / 2)..(x + rfun K t / 2),
            (1 + (1 / (30 * Real.sqrt (K : ℝ))) * ∑ l ∈ range K,
              (((1 : ℝ) + (l : ℝ) / (K : ℝ)) * (coef K l).1.re)
                * Real.cos (((K + l : ℕ) : ℝ) * (2 * Real.pi) * y)) := by
      rw [funext hpt]
    rw [h1]
    rw [intervalIntegral.integral_add intervalIntegrable_const
      ((hsumcont.const_mul _).intervalIntegrable _ _)]
    rw [intervalIntegral.integral_const, intervalIntegral.integral_const_mul, hsum]
    have hlen : ((x + rfun K t / 2) - (x - rfun K t / 2)) • (1 : ℝ) = rfun K t := by
      simp only [smul_eq_mul, mul_one]
      ring
    rw [hlen]
  rw [hInt]
  have hterm : ∀ l ∈ range K,
      (1 / (30 * Real.sqrt (K : ℝ)))
          * ((((1 : ℝ) + (l : ℝ) / (K : ℝ)) * (coef K l).1.re)
            * (Real.cos (((K + l : ℕ) : ℝ) * (2 * Real.pi) * x)
              * (Real.sin (Real.pi * ((K + l : ℕ) : ℝ) * rfun K t)
                / (Real.pi * ((K + l : ℕ) : ℝ)))))
        = (1 / (30 * Real.pi * (K : ℝ) * Real.sqrt (K : ℝ)))
          * ((coef K l).1.re * (-1 : ℝ) ^ (K + l)
              * Real.sin (2 * Real.pi * t * (1 + (l : ℝ) / (K : ℝ)))
              * Real.cos (((K + l : ℕ) : ℝ) * (2 * Real.pi) * x)) := by
    intro l _
    have h := average_term' hK t x l
    rw [← h]
    ring
  calc rfun K t + (1 / (30 * Real.sqrt (K : ℝ))) * ∑ l ∈ range K,
        (((1 : ℝ) + (l : ℝ) / (K : ℝ)) * (coef K l).1.re)
          * (Real.cos (((K + l : ℕ) : ℝ) * (2 * Real.pi) * x)
            * (Real.sin (Real.pi * ((K + l : ℕ) : ℝ) * rfun K t)
              / (Real.pi * ((K + l : ℕ) : ℝ))))
      = rfun K t + ∑ l ∈ range K, (1 / (30 * Real.sqrt (K : ℝ)))
          * ((((1 : ℝ) + (l : ℝ) / (K : ℝ)) * (coef K l).1.re)
            * (Real.cos (((K + l : ℕ) : ℝ) * (2 * Real.pi) * x)
              * (Real.sin (Real.pi * ((K + l : ℕ) : ℝ) * rfun K t)
                / (Real.pi * ((K + l : ℕ) : ℝ))))) := by
        rw [Finset.mul_sum]
    _ = rfun K t + ∑ l ∈ range K,
          (1 / (30 * Real.pi * (K : ℝ) * Real.sqrt (K : ℝ)))
            * ((coef K l).1.re * (-1 : ℝ) ^ (K + l)
                * Real.sin (2 * Real.pi * t * (1 + (l : ℝ) / (K : ℝ)))
                * Real.cos (((K + l : ℕ) : ℝ) * (2 * Real.pi) * x)) := by
        rw [Finset.sum_congr rfl hterm]
    _ = rfun K t + Sfun K t x / (30 * Real.pi * (K : ℝ) * Real.sqrt (K : ℝ)) := by
        congr 1
        rw [show Sfun K t x = ∑ l ∈ range K,
            ((coef K l).1.re * (-1 : ℝ) ^ (K + l)
              * Real.sin (2 * Real.pi * t * (1 + (l : ℝ) / (K : ℝ))))
              * Real.cos (((K + l : ℕ) : ℝ) * (2 * Real.pi) * x) from rfl]
        symm
        rw [div_eq_inv_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl (fun l _ => by rw [one_div])


/-- **Equation (3.1) as displayed**: the normalised average is `1 + d_t` with
`d_t = S_t/(30πK^{3/2} r(t))`. -/
theorem average_rho {K : ℕ} (hK : 1 ≤ K) (t x : ℝ) (hr : 0 < rfun K t) :
    (1 / rfun K t)
        * ∫ y in (x - rfun K t / 2)..(x + rfun K t / 2), rho K y
      = 1 + Sfun K t x
          / (30 * Real.pi * (K : ℝ) * Real.sqrt (K : ℝ) * rfun K t) := by
  rw [integral_rho_shift hK t x hr]
  field_simp

end RudinDensity
end CenteredCube

#print axioms CenteredCube.RudinDensity.average_cos
#print axioms CenteredCube.RudinDensity.sin_pi_mul_rfun
#print axioms CenteredCube.RudinDensity.average_term'
#print axioms CenteredCube.RudinDensity.integral_cos_shift
#print axioms CenteredCube.RudinDensity.integral_cos_sum_shift
#print axioms CenteredCube.RudinDensity.integral_rho_shift
#print axioms CenteredCube.RudinDensity.average_rho
