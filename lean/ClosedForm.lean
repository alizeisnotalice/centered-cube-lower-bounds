/-
The closed form of the finite-band kernel (equation (3.5) of the manuscript).

`D_K(τ) = (1/K) ∑_{l<K} e^{2πiτ(1+l/K)}`.  Writing `ζ = e^{2πiτ/K}`, the geometric
sum gives `∑_{l<K} ζ^l = (ζ^K − 1)/(ζ − 1)` with `ζ^K = e^{2πiτ}`, and the identity

  `e^{iθ} − 1 = e^{iθ/2} · 2i sin(θ/2)`

turns the ratio into a pure sine quotient, yielding

  `D_K(τ) = (1/K) e^{iπ(3−1/K)τ} sin(πτ)/sin(πτ/K)`   (`sin(πτ/K) ≠ 0`),
  `|D_K(τ)| = |sin(πτ)| / (K |sin(πτ/K)|)`.

This is the input for the scale-kernel bounds of `lem:finite-kernel`; the bound
itself is not proved here.
-/
import Window

open Finset Complex
open scoped BigOperators

namespace CenteredCube
namespace RudinDensity

/-- `e^{iθ}`, abbreviations to keep elaboration cheap. -/
noncomputable abbrev eI (θ : ℝ) : ℂ := Complex.exp ((θ : ℂ) * Complex.I)

/-- Regrouping of four factors. -/
theorem mul_assoc4 (w x y z : ℂ) : w * x * (y * z) = w * (x * y) * z := by ring

/-- `e^{iθ} − 1 = e^{iθ/2} · (I · 2 sin(θ/2))`. -/
theorem exp_mul_I_sub_one (θ : ℝ) :
    eI θ - 1 = eI (θ / 2) * (Complex.I * ((2 * Real.sin (θ / 2) : ℝ) : ℂ)) := by
  have hc : Real.cos θ = 2 * Real.cos (θ / 2) ^ 2 - 1 := by
    conv_lhs => rw [show (θ : ℝ) = 2 * (θ / 2) by ring]
    exact Real.cos_two_mul _
  have hs : Real.sin θ = 2 * Real.sin (θ / 2) * Real.cos (θ / 2) := by
    conv_lhs => rw [show (θ : ℝ) = 2 * (θ / 2) by ring]
    exact Real.sin_two_mul _
  unfold eI
  rw [Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I]
  apply Complex.ext
  · simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.mul_re, Complex.mul_im, Complex.one_re,
      Complex.sub_im, Complex.add_im, mul_zero, mul_one, add_zero,
      zero_add, sub_zero, zero_mul, Complex.ofReal_one, Complex.ofReal_mul]
    rw [hc]
    nlinarith [Real.sin_sq_add_cos_sq (θ / 2)]
  · simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.mul_re, Complex.mul_im, Complex.one_re,
      Complex.one_im, Complex.sub_im, Complex.add_im, mul_zero, mul_one, add_zero,
      zero_add, sub_zero, zero_mul, Complex.ofReal_one, Complex.ofReal_mul]
    rw [hs]
    ring

/-- **Ratio form**: `(e^{iθ}−1)/(e^{iφ}−1) = e^{i(θ−φ)/2} · sin(θ/2)/sin(φ/2)`. -/
theorem exp_ratio {θ φ : ℝ} (h : Real.sin (φ / 2) ≠ 0) :
    (eI θ - 1) / (eI φ - 1)
      = eI ((θ - φ) / 2) * ((Real.sin (θ / 2) / Real.sin (φ / 2) : ℝ) : ℂ) := by
  have h1 := exp_mul_I_sub_one θ
  have h2 := exp_mul_I_sub_one φ
  rw [h1, h2]
  have hne2 : (2 * Real.sin (φ / 2) : ℝ) ≠ 0 := by positivity
  have heq : (eI (θ / 2) * (Complex.I * ((2 * Real.sin (θ / 2) : ℝ) : ℂ)))
      * (eI (φ / 2) * (Complex.I * ((2 * Real.sin (φ / 2) : ℝ) : ℂ)))⁻¹
      = eI ((θ - φ) / 2) * ((Real.sin (θ / 2) / Real.sin (φ / 2) : ℝ) : ℂ) := by
    have hI : (Complex.I * ((2 * Real.sin (θ / 2) : ℝ) : ℂ))
        * (Complex.I * ((2 * Real.sin (φ / 2) : ℝ) : ℂ))⁻¹
        = ((Real.sin (θ / 2) / Real.sin (φ / 2) : ℝ) : ℂ) := by
      field_simp [hne2]
      push_cast
      ring
    have hexp : eI (θ / 2) * (eI (φ / 2))⁻¹ = eI ((θ - φ) / 2) := by
      unfold eI
      rw [← Complex.exp_neg, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    have hswap : (a b c d : ℂ) → a * b * (c * d)⁻¹ = a * c⁻¹ * (b * d⁻¹) := by
      intro a b c d
      rw [mul_inv_rev]
      ring_nf
    rw [hswap, hexp, hI]
  rw [div_eq_mul_inv, heq]


/-- Geometric factorisation of `D_K`: `(1/K) e^{2πiτ} ∑_{l<K} ζ^l` with `ζ = e^{2πiτ/K}`. -/
theorem DK_factor (K : ℕ) (τ : ℝ) :
    DK K τ = (1 / (K : ℂ)) * eI (2 * Real.pi * τ)
        * ∑ l ∈ range K, (eI (2 * Real.pi * τ / (K : ℝ))) ^ l := by
  unfold DK
  have hsum : (∑ l ∈ range K,
        Complex.exp (((2 * Real.pi * τ * (1 + (l : ℝ) / (K : ℝ)) : ℝ) : ℂ) * Complex.I))
      = eI (2 * Real.pi * τ) * ∑ l ∈ range K, (eI (2 * Real.pi * τ / (K : ℝ))) ^ l := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    have harg : (2 * Real.pi * τ * (1 + (l : ℝ) / (K : ℝ)) : ℝ)
        = 2 * Real.pi * τ + l * (2 * Real.pi * τ / (K : ℝ)) := by field_simp
    have hadd : Complex.exp (((2 * Real.pi * τ * (1 + (l : ℝ) / (K : ℝ)) : ℝ) : ℂ) * Complex.I)
        = Complex.exp (((2 * Real.pi * τ : ℝ) : ℂ) * Complex.I)
            * Complex.exp (((l * (2 * Real.pi * τ / (K : ℝ)) : ℝ) : ℂ) * Complex.I) := by
      rw [harg, Complex.ofReal_add, add_mul, Complex.exp_add]
    have hpow : Complex.exp (((l * (2 * Real.pi * τ / (K : ℝ)) : ℝ) : ℂ) * Complex.I)
        = (Complex.exp (((2 * Real.pi * τ / (K : ℝ) : ℝ) : ℂ) * Complex.I)) ^ l := by
      rw [show ((l * (2 * Real.pi * τ / (K : ℝ)) : ℝ) : ℂ) * Complex.I
          = ((l : ℂ)) * (((2 * Real.pi * τ / (K : ℝ) : ℝ) : ℂ) * Complex.I) by
            push_cast
            ring,
        Complex.exp_nat_mul]
    rw [hadd, hpow]
  rw [hsum]
  rw [← mul_assoc]


/-- **Equation (3.5), the closed form**:
`D_K(τ) = (1/K) e^{iπ(3−1/K)τ} sin(πτ)/sin(πτ/K)` when `sin(πτ/K) ≠ 0`. -/
theorem DK_closed {K : ℕ} (hK : 1 ≤ K) {τ : ℝ}
    (hs : Real.sin (Real.pi * τ / (K : ℝ)) ≠ 0) :
    DK K τ = (1 / (K : ℂ)) * eI (Real.pi * (3 - 1 / (K : ℝ)) * τ)
        * ((Real.sin (Real.pi * τ) / Real.sin (Real.pi * τ / (K : ℝ)) : ℝ) : ℂ) := by
  have hK0 : ((K : ℕ) : ℝ) ≠ 0 := by positivity
  have hdiv : (2 * Real.pi * τ / (K : ℝ) : ℝ) / 2 = Real.pi * τ / (K : ℝ) := by
    field_simp
  have hKc : (((K : ℕ) : ℂ)) ≠ 0 := by exact_mod_cast hK0
  have hqK : (eI (2 * Real.pi * τ / (K : ℝ))) ^ K = eI (2 * Real.pi * τ) := by
    unfold eI
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    field_simp [hK0]

  have hne : eI (2 * Real.pi * τ / (K : ℝ)) ≠ 1 := by
    intro h
    have : ‖eI (2 * Real.pi * τ / (K : ℝ)) - 1‖ = 0 := by
      rw [h, sub_self, norm_zero]
    unfold eI at this
    rw [show ((2 * Real.pi * τ / (K : ℝ) : ℝ) : ℂ) * Complex.I
        = Complex.I * ((2 * Real.pi * τ / (K : ℝ) : ℝ) : ℂ) from mul_comm _ _,
      Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, abs_mul,
      abs_of_pos (by norm_num : (0:ℝ) < 2)] at this
    rw [hdiv] at this
    have : |Real.sin (Real.pi * τ / (K : ℝ))| = 0 := by linarith
    exact hs (abs_eq_zero.mp this)
  have hgeom : ∑ l ∈ range K, (eI (2 * Real.pi * τ / (K : ℝ))) ^ l
      = ((eI (2 * Real.pi * τ / (K : ℝ))) ^ K - 1) / (eI (2 * Real.pi * τ / (K : ℝ)) - 1) :=
    geom_sum_eq hne K
  rw [DK_factor]
  rw [hgeom]
  rw [hqK]
  have hratio : (eI (2 * Real.pi * τ) - 1) / (eI (2 * Real.pi * τ / (K : ℝ)) - 1)
      = eI ((2 * Real.pi * τ - 2 * Real.pi * τ / (K : ℝ)) / 2)
          * ((Real.sin (2 * Real.pi * τ / 2) / Real.sin (2 * Real.pi * τ / (K : ℝ) / 2) : ℝ) : ℂ) :=
    exp_ratio (θ := 2 * Real.pi * τ) (φ := 2 * Real.pi * τ / (K : ℝ)) (by { rw [hdiv]; exact hs })
  have hsin : Real.sin (2 * Real.pi * τ / 2) = Real.sin (Real.pi * τ) := by
    congr 1
    ring
  have hsin2 : Real.sin (2 * Real.pi * τ / (K : ℝ) / 2) = Real.sin (Real.pi * τ / (K : ℝ)) := by
    rw [hdiv]
  rw [hratio, hsin, hsin2]
  have hexp0 : eI (2 * Real.pi * τ)
      * eI ((2 * Real.pi * τ - 2 * Real.pi * τ / (K : ℝ)) / 2)
      = eI (Real.pi * (3 - 1 / (K : ℝ)) * τ) := by
    unfold eI
    rw [← Complex.exp_add]
    congr 1
    push_cast
    field_simp [hK0]
    ring
  have hreassoc : (1 / (K : ℂ)) * eI (2 * Real.pi * τ)
        * (eI ((2 * Real.pi * τ - 2 * Real.pi * τ / (K : ℝ)) / 2)
          * ((Real.sin (Real.pi * τ) / Real.sin (Real.pi * τ / (K : ℝ)) : ℝ) : ℂ))
      = (1 / (K : ℂ)) * (eI (2 * Real.pi * τ)
          * eI ((2 * Real.pi * τ - 2 * Real.pi * τ / (K : ℝ)) / 2))
        * ((Real.sin (Real.pi * τ) / Real.sin (Real.pi * τ / (K : ℝ)) : ℝ) : ℂ) :=
    mul_assoc4 _ _ _ _
  rw [hreassoc, hexp0]


/-- **The modulus formula (3.5)**: `|D_K(τ)| = |sin(πτ)| / (K |sin(πτ/K)|)`. -/
theorem norm_DK_eq {K : ℕ} (hK : 1 ≤ K) {τ : ℝ}
    (hs : Real.sin (Real.pi * τ / (K : ℝ)) ≠ 0) :
    ‖DK K τ‖ = |Real.sin (Real.pi * τ)|
      / (((K : ℕ) : ℝ) * |Real.sin (Real.pi * τ / (K : ℝ))|) := by
  have hK0 : (0 : ℝ) < ((K : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < K)
  rw [DK_closed hK hs, norm_mul, norm_mul]
  have h1 : ‖(1 / (K : ℂ))‖ = 1 / ((K : ℕ) : ℝ) := by
    rw [norm_div, norm_one, Complex.norm_natCast]
  have h2 : ‖eI (Real.pi * (3 - 1 / (K : ℝ)) * τ)‖ = 1 := by
    unfold eI
    exact Complex.norm_exp_ofReal_mul_I _
  have h3 : ‖((Real.sin (Real.pi * τ) / Real.sin (Real.pi * τ / (K : ℝ)) : ℝ) : ℂ)‖
      = |Real.sin (Real.pi * τ) / Real.sin (Real.pi * τ / (K : ℝ))| :=
    Complex.norm_real _
  rw [h1, h2, h3, mul_one, abs_div]
  field_simp

end RudinDensity
end CenteredCube

#print axioms CenteredCube.RudinDensity.mul_assoc4
#print axioms CenteredCube.RudinDensity.exp_mul_I_sub_one
#print axioms CenteredCube.RudinDensity.exp_ratio
#print axioms CenteredCube.RudinDensity.DK_factor
#print axioms CenteredCube.RudinDensity.DK_closed
#print axioms CenteredCube.RudinDensity.norm_DK_eq
