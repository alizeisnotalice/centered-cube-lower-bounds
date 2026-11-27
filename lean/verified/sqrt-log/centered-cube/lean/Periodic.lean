/-
Periodic functions and the mass of the truncated test function.

The `√n/log n` manuscript truncates the `ℤⁿ`-periodic lift `H̃_n` to the box
`[-R,R]ⁿ` and uses

  `‖f_n‖₁ = (2R)ⁿ`,  `R = n²`,

because the lift has mass one per unit cell.  This file proves the one-dimensional
input, in the general form used by the manuscript:

* `zof_add_one`, `rho_add_one`: `ρ_K` is `1`-periodic;
* `integral_periodic_nat`: `∫₀^N f = N ∫₀¹ f` for a `1`-periodic `f`;
* `integral_periodic_symmetric`: `∫_{-R}^{R} f = 2R ∫₀¹ f`;
* `integral_rho_box`: the one-dimensional mass `∫_{-R}^{R} ρ_K = 2R`.

The `n`-dimensional statement `∫_{[-R,R]ⁿ} ∏ρ(x_i) = (2R)ⁿ` is the Fubini
product of the last item; that product step is not formalized here.
-/
import RhoNormalise

open MeasureTheory intervalIntegral Finset

namespace CenteredCube
namespace RudinDensity

/-- `zof` is `1`-periodic. -/
theorem zof_add_one (x : ℝ) : zof (x + 1) = zof x := by
  unfold zof
  rw [show (2 * (Real.pi : ℂ) * Complex.I * ((x + 1 : ℝ) : ℂ))
      = 2 * (Real.pi : ℂ) * Complex.I * (x : ℂ) + 2 * (Real.pi : ℂ) * Complex.I * 1 by
    push_cast; ring]
  rw [Complex.exp_add]
  have h1 : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * 1) = 1 := by
    rw [show (2 * (Real.pi : ℂ) * Complex.I * 1)
        = ((2 * Real.pi : ℝ) : ℂ) * Complex.I by push_cast; ring]
    rw [Complex.exp_ofReal_mul_I]
    simp [Real.cos_two_pi, Real.sin_two_pi]
  rw [h1, mul_one]

/-- The density `ρ_K` is `1`-periodic. -/
theorem rho_add_one (K : ℕ) (x : ℝ) : rho K (x + 1) = rho K x := by
  unfold rho
  rw [zof_add_one]

/-- Iterating `1`-periodicity: `f (x + N) = f x` for `N ∈ ℕ`. -/
theorem periodic_add_nat {f : ℝ → ℝ} (hf : ∀ x, f (x + 1) = f x) :
    ∀ (N : ℕ) (x : ℝ), f (x + N) = f x
  | 0, x => by simp
  | N + 1, x => by
    rw [show x + (N + 1 : ℕ) = (x + N) + 1 by push_cast; ring, hf, periodic_add_nat hf N x]

/-- `∫₀^N f = N ∫₀¹ f` for a `1`-periodic `f`. -/
theorem integral_periodic_nat {f : ℝ → ℝ} (hf : ∀ x, f (x + 1) = f x) (hint : ∀ a b : ℝ,
    IntervalIntegrable f volume a b) :
    ∀ N : ℕ, ∫ x in (0 : ℝ)..(N : ℝ), f x = (N : ℝ) * ∫ x in (0 : ℝ)..1, f x
  | 0 => by simp
  | N + 1 => by
    have hcast : (((N + 1 : ℕ)) : ℝ) = (N : ℝ) + 1 := by push_cast; ring
    have hper : ∀ x : ℝ, f ((N : ℝ) + x) = f x := by
      intro x
      rw [add_comm]
      exact periodic_add_nat hf N x
    have hshift : ∫ x in ((N : ℝ))..((N : ℝ) + 1), f x = ∫ x in (0 : ℝ)..1, f x := by
      have h1 : ∫ x in (0 : ℝ)..1, f ((N : ℝ) + x) = ∫ x in ((N : ℝ))..((N : ℝ) + 1), f x := by
        have h := intervalIntegral.integral_comp_add_left (f := f) (a := (0 : ℝ)) (b := 1) (d := (N : ℝ))
        rw [show (N : ℝ) + 0 = (N : ℝ) by ring] at h
        exact h
      rw [← h1]
      simp only [hper]
    rw [hcast, ← intervalIntegral.integral_add_adjacent_intervals (hint 0 (N : ℝ))
      (hint (N : ℝ) ((N : ℝ) + 1)), integral_periodic_nat hf hint N, hshift]
    push_cast
    ring


/-- `ρ_K` is continuous: by `weightedSum_eq_series` it is a trigonometric
polynomial in `z = e^{2πix}`. -/
theorem continuous_rho {K : ℕ} (hK : 1 ≤ K) : Continuous (rho K) := by
  have hW : ∀ z : ℂ, weightedSum z K
      = ∑ l ∈ range K, ((1 : ℂ) + (l : ℂ) / (K : ℂ)) * ((coef K l).1 * z ^ l) :=
    fun z => weightedSum_eq_series hK z
  have hfun : rho K = fun x : ℝ => 1 + (1 / (30 * Real.sqrt (K : ℝ))) *
      Complex.re ((zof x) ^ K * ∑ l ∈ range K,
        ((1 : ℂ) + (l : ℂ) / (K : ℂ)) * ((coef K l).1 * (zof x) ^ l)) := by
    funext x
    rw [rho, hW (zof x)]
  have hsum : Continuous fun x : ℝ => ∑ l ∈ range K,
      ((1 : ℂ) + (l : ℂ) / (K : ℂ)) * ((coef K l).1 * (zof x) ^ l) := by
    refine continuous_finset_sum_interval _ (fun l _ => ?_)
    unfold zof
    fun_prop
  rw [hfun]
  unfold zof
  fun_prop

/-- `f (x - N) = f x` for a `1`-periodic `f`. -/
theorem periodic_sub_nat {f : ℝ → ℝ} (hf : ∀ x, f (x + 1) = f x) :
    ∀ (N : ℕ) (x : ℝ), f (x - N) = f x
  | 0, x => by simp
  | N + 1, x => by
    rw [show x - ((N + 1 : ℕ) : ℝ) = (x - (N : ℝ)) - 1 by push_cast; ring]
    rw [(hf ((x - (N : ℝ)) - 1)).symm]
    rw [show (x - (N : ℝ)) - 1 + 1 = x - (N : ℝ) by ring]
    exact periodic_sub_nat hf N x

/-- `∫_{-N}^{0} f = N ∫₀¹ f` for a `1`-periodic `f`. -/
theorem integral_periodic_neg {f : ℝ → ℝ} (hf : ∀ x, f (x + 1) = f x)
    (hint : ∀ a b : ℝ, IntervalIntegrable f volume a b) (N : ℕ) :
    ∫ x in (-(N : ℝ))..0, f x = (N : ℝ) * ∫ x in (0 : ℝ)..1, f x := by
  have h1 : ∫ x in (0 : ℝ)..(N : ℝ), f (-(N : ℝ) + x) = ∫ x in (-(N : ℝ))..0, f x := by
    have h := intervalIntegral.integral_comp_add_left (f := f) (a := (0 : ℝ)) (b := (N : ℝ))
      (d := -(N : ℝ))
    rw [show -(N : ℝ) + 0 = -(N : ℝ) by ring, show -(N : ℝ) + (N : ℝ) = 0 by ring] at h
    exact h
  rw [← h1]
  have hper : ∀ x : ℝ, f (-(N : ℝ) + x) = f x := by
    intro x
    rw [show -(N : ℝ) + x = x - (N : ℝ) by ring]
    exact periodic_sub_nat hf N x
  simp only [hper]
  exact integral_periodic_nat hf hint N

/-- The one-dimensional mass of the truncated density: `∫_{-R}^{R} ρ_K = 2R`. -/
theorem integral_rho_box {K : ℕ} (hK : 1 ≤ K) (R : ℕ) :
    ∫ x in (-(R : ℝ))..(R : ℝ), rho K x = 2 * (R : ℝ) := by
  have hint : ∀ a b : ℝ, IntervalIntegrable (rho K) volume a b :=
    fun a b => (continuous_rho hK).intervalIntegrable a b
  rw [← intervalIntegral.integral_add_adjacent_intervals (hint (-(R : ℝ)) 0) (hint 0 (R : ℝ))]
  rw [integral_periodic_neg (rho_add_one K) hint R, integral_periodic_nat (rho_add_one K) hint R,
    integral_rho K hK]
  ring

end RudinDensity
end CenteredCube

#print axioms CenteredCube.RudinDensity.zof_add_one
#print axioms CenteredCube.RudinDensity.rho_add_one
#print axioms CenteredCube.RudinDensity.integral_periodic_nat
#print axioms CenteredCube.RudinDensity.continuous_rho
#print axioms CenteredCube.RudinDensity.integral_periodic_neg
#print axioms CenteredCube.RudinDensity.integral_rho_box
