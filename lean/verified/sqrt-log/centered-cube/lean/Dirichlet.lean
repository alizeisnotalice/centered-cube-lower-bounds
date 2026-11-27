/-
The finite-band Dirichlet kernel `D_K` of the manuscript, and eq. (3.4):
`∫₀¹ S_t S_s = (K/4)[Re D_K(t−s) − Re D_K(t+s)]`.

`D_K(τ) = (1/K) ∑_{l<K} e^{2πiτ(1+l/K)}`, `Re D_K(τ) = (1/K) ∑_{l<K} cos(2πτ(1+l/K))`.
Since `2 sin A sin B = cos(A−B) − cos(A+B)`, the variance/covariance formula
`∫₀¹ S_t S_s = ½ ∑ sin_t sin_s` of `Variance.lean` becomes

  `¼ ∑_l cos(2π(t−s)(1+l/K)) − ¼ ∑_l cos(2π(t+s)(1+l/K))
     = (K/4)[Re D_K(t−s) − Re D_K(t+s)]`.

Also `|D_K(τ)| ≤ 1` (an average of `K` unit complex numbers), which is the bound
used for the scale covariance.  The closed form
`D_K(τ) = e^{πi(3−1/K)τ} sin(πτ)/(K sin(πτ/K))` of eq. (3.5) is *not* proved here.
-/
import Bounded

open Finset MeasureTheory intervalIntegral
open scoped BigOperators

namespace CenteredCube
namespace RudinDensity

/-- The finite-band kernel `D_K(τ) = (1/K)∑_{l<K} e^{2πiτ(1+l/K)}`. -/
noncomputable def DK (K : ℕ) (τ : ℝ) : ℂ :=
  (1 / (K : ℂ)) * ∑ l ∈ range K,
    Complex.exp (((2 * Real.pi * τ * (1 + (l : ℝ) / (K : ℝ)) : ℝ) : ℂ) * Complex.I)

/-- Its real part. -/
noncomputable def ReDK (K : ℕ) (τ : ℝ) : ℝ := (DK K τ).re

/-- `Re D_K(τ) = (1/K) ∑_{l<K} cos(2πτ(1+l/K))`. -/
theorem ReDK_eq (K : ℕ) (τ : ℝ) :
    ReDK K τ = (1 / (K : ℝ)) * ∑ l ∈ range K,
      Real.cos (2 * Real.pi * τ * (1 + (l : ℝ) / (K : ℝ))) := by
  unfold ReDK DK
  have hre : ((1 : ℂ) / (K : ℂ)).re = 1 / (K : ℝ) := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_one, ← Complex.ofReal_div]
    simp
  have him : ((1 : ℂ) / (K : ℂ)).im = 0 := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_one, ← Complex.ofReal_div]
    simp
  rw [Complex.mul_re, hre, him, zero_mul, sub_zero, Complex.re_sum]
  congr 1
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [Complex.exp_ofReal_mul_I]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_one,
    mul_zero, add_zero, zero_add, sub_zero]

/-- `2 sin A sin B = cos(A−B) − cos(A+B)`. -/
theorem two_mul_sin_mul_sin (A B : ℝ) :
    2 * (Real.sin A * Real.sin B) = Real.cos (A - B) - Real.cos (A + B) := by
  have h1 := Real.cos_sub A B
  have h2 := Real.cos_add A B
  linarith

/-- **`eq:exact-covariance`**: `∫₀¹ S_t S_s = (K/4)[Re D_K(t−s) − Re D_K(t+s)]`. -/
theorem integral_Sfun_mul_eq_DK {K : ℕ} (hK : 1 ≤ K) (t s : ℝ) :
    ∫ x in (0 : ℝ)..1, Sfun K t x * Sfun K s x
      = (K : ℝ) / 4 * (ReDK K (t - s) - ReDK K (t + s)) := by
  have hK0 : ((K : ℕ) : ℝ) ≠ 0 := by positivity
  rw [integral_Sfun_mul hK t s, Finset.mul_sum]
  have hterm : ∀ l ∈ range K,
      (1 / 2 : ℝ) * (Real.sin (2 * Real.pi * t * (1 + (l : ℝ) / (K : ℝ)))
          * Real.sin (2 * Real.pi * s * (1 + (l : ℝ) / (K : ℝ))))
        = 1 / 4 * Real.cos (2 * Real.pi * (t - s) * (1 + (l : ℝ) / (K : ℝ)))
          - 1 / 4 * Real.cos (2 * Real.pi * (t + s) * (1 + (l : ℝ) / (K : ℝ))) := by
    intro l _
    have hs := two_mul_sin_mul_sin (2 * Real.pi * t * (1 + (l : ℝ) / (K : ℝ)))
      (2 * Real.pi * s * (1 + (l : ℝ) / (K : ℝ)))
    have e1 : 2 * Real.pi * t * (1 + (l : ℝ) / (K : ℝ))
        - 2 * Real.pi * s * (1 + (l : ℝ) / (K : ℝ))
        = 2 * Real.pi * (t - s) * (1 + (l : ℝ) / (K : ℝ)) := by ring
    have e2 : 2 * Real.pi * t * (1 + (l : ℝ) / (K : ℝ))
        + 2 * Real.pi * s * (1 + (l : ℝ) / (K : ℝ))
        = 2 * Real.pi * (t + s) * (1 + (l : ℝ) / (K : ℝ)) := by ring
    rw [e1, e2] at hs
    linarith
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, ReDK_eq, ReDK_eq]
  field_simp


/-- `|D_K(τ)| ≤ 1`: an average of `K` unit complex numbers. -/
theorem norm_DK_le {K : ℕ} (hK : 0 < K) (τ : ℝ) : ‖DK K τ‖ ≤ 1 := by
  have hK0 : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  have hsum : ‖∑ l ∈ range K,
      Complex.exp (((2 * Real.pi * τ * (1 + (l : ℝ) / (K : ℝ)) : ℝ) : ℂ) * Complex.I)‖
      ≤ (K : ℝ) := by
    refine (norm_sum_le _ _).trans ?_
    have h1 : ∀ l ∈ range K,
        ‖Complex.exp (((2 * Real.pi * τ * (1 + (l : ℝ) / (K : ℝ)) : ℝ) : ℂ) * Complex.I)‖
          = (1 : ℝ) := fun l _ => Complex.norm_exp_ofReal_mul_I _
    rw [Finset.sum_congr rfl h1]
    simp
  unfold DK
  rw [norm_mul, norm_div, norm_one, Complex.norm_natCast]
  calc 1 / (K : ℝ) * ‖∑ l ∈ range K,
        Complex.exp (((2 * Real.pi * τ * (1 + (l : ℝ) / (K : ℝ)) : ℝ) : ℂ) * Complex.I)‖
      ≤ 1 / (K : ℝ) * (K : ℝ) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 1 := by field_simp

end RudinDensity
end CenteredCube

#print axioms CenteredCube.RudinDensity.ReDK_eq
#print axioms CenteredCube.RudinDensity.two_mul_sin_mul_sin
#print axioms CenteredCube.RudinDensity.integral_Sfun_mul_eq_DK
#print axioms CenteredCube.RudinDensity.norm_DK_le
