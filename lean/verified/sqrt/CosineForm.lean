/-
The real cosine form of the Rudin–Shapiro density.

The manuscript displays (eq. (1.2))

  `ρ_K(x) = 1 + (1/(30√K)) ∑_{l<K} ε_l (1 + l/K) cos(2π(K+l)x)`,

with `ε_l ∈ {±1}`.  The formal definition in `Abel.lean` writes `ρ_K` through the
complex exponential, `ρ_K = 1 + Re(z^K W_K(z))/(30√K)`, `z = e^{2πix}`.  This file
identifies the two, which is the input to the exact one-dimensional average
(eq. (3.1)) and to the covariance computation.

* `zof_pow_eq`: `(e^{2πix})^m = cos(2πmx) + i sin(2πmx)`;
* `re_ofReal_mul_zof_pow`: `Re(r e^{2πimx}) = r cos(2πmx)` for real `r`;
* `rho_eq_cos_series`: the displayed formula for `ρ_K`.
-/
import Abel
import Trig
import RhoNormalise

open MeasureTheory intervalIntegral Finset
open scoped BigOperators

namespace CenteredCube
namespace RudinDensity

/-- `(e^{2πix})^m = cos(2πmx) + i sin(2πmx)`. -/
theorem zof_pow_eq (m : ℕ) (x : ℝ) :
    (zof x) ^ m = ((Real.cos ((m : ℝ) * (2 * Real.pi) * x) : ℂ)
      + (Real.sin ((m : ℝ) * (2 * Real.pi) * x) : ℂ) * Complex.I) := by
  rw [zof, ← Complex.exp_nat_mul]
  rw [show (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I * (x : ℂ))
      = (((m : ℝ) * (2 * Real.pi) * x : ℝ) : ℂ) * Complex.I by push_cast; ring]
  rw [Complex.exp_ofReal_mul_I]

/-- `Re(r e^{2πimx}) = r cos(2πmx)` for real `r`. -/
theorem re_ofReal_mul_zof_pow (r : ℝ) (m : ℕ) (x : ℝ) :
    Complex.re ((r : ℂ) * (zof x) ^ m) = r * Real.cos ((m : ℝ) * (2 * Real.pi) * x) := by
  rw [zof_pow_eq m x]
  simp only [Complex.mul_re, Complex.add_re, Complex.add_im, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, sub_zero, add_zero]
  ring

/-- **The displayed cosine series** for `ρ_K`. -/
theorem rho_eq_cos_series {K : ℕ} (hK : 1 ≤ K) (x : ℝ) :
    rho K x = 1 + (1 / (30 * Real.sqrt (K : ℝ))) *
      ∑ l ∈ range K,
        (((1 : ℝ) + (l : ℝ) / (K : ℝ)) * (coef K l).1.re)
          * Real.cos (((K + l : ℕ) : ℝ) * (2 * Real.pi) * x) := by
  have hcoef : ∀ l ∈ range K, (coef K l).1 = (((coef K l).1.re : ℝ) : ℂ) := by
    intro l hl
    have hK2 : l < 2 ^ K := lt_of_lt_of_le (Finset.mem_range.mp hl) (le_two_pow_self K)
    rcases (coef_unit K l hK2).1 with h | h <;> simp [h]
  have hterm : ∀ l ∈ range K,
      Complex.re ((zof x) ^ K
          * (((1 : ℂ) + (l : ℂ) / (K : ℂ)) * ((coef K l).1 * (zof x) ^ l)))
        = (((1 : ℝ) + (l : ℝ) / (K : ℝ)) * (coef K l).1.re)
          * Real.cos (((K + l : ℕ) : ℝ) * (2 * Real.pi) * x) := by
    intro l hl
    rw [hcoef l hl]
    have h1 : ((1 : ℂ) + (l : ℂ) / (K : ℂ)) = (((1 : ℝ) + (l : ℝ) / (K : ℝ) : ℝ) : ℂ) := by
      push_cast; ring
    rw [h1]
    rw [show (zof x) ^ K
          * ((↑((1 : ℝ) + (l : ℝ) / (K : ℝ)) : ℂ) * ((↑((coef K l).1.re) : ℂ) * (zof x) ^ l))
        = (↑(((1 : ℝ) + (l : ℝ) / (K : ℝ)) * ((coef K l).1.re)) : ℂ) * (zof x) ^ (K + l) by
      rw [pow_add]
      push_cast
      ring]
    exact re_ofReal_mul_zof_pow _ _ _
  rw [rho, weightedSum_eq_series hK (zof x)]
  rw [show (zof x) ^ K * ∑ l ∈ range K, ((1 : ℂ) + (l : ℂ) / (K : ℂ)) * ((coef K l).1 * (zof x) ^ l)
      = ∑ l ∈ range K, (zof x) ^ K
          * (((1 : ℂ) + (l : ℂ) / (K : ℂ)) * ((coef K l).1 * (zof x) ^ l)) from by
    rw [Finset.mul_sum]]
  rw [re_finset_sum]
  rw [Finset.sum_congr rfl hterm]

end RudinDensity
end CenteredCube

#print axioms CenteredCube.RudinDensity.zof_pow_eq
#print axioms CenteredCube.RudinDensity.re_ofReal_mul_zof_pow
#print axioms CenteredCube.RudinDensity.rho_eq_cos_series
