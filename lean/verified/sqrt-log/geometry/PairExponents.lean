import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic

namespace CenteredCube.RudinDensity

theorem reciprocal_near {κ τ : ℝ} (hden : 0 < 1 + κ)
    (hκ : κ ≤ 1 - 4 * τ^2) :
    1 / 2 + τ^2 ≤ 1 / (1 + κ) := by
  have hb : 0 < 2 - 4 * τ^2 := by linarith
  calc
    1 / 2 + τ^2 ≤ 1 / (2 - 4 * τ^2) := by
      apply (le_div_iff₀ hb).2
      rw [show (1 / 2 + τ^2) * (2 - 4 * τ^2) = 1 - 4 * (τ ^ 2)^2 by ring]
      linarith [sq_nonneg (τ^2)]
    _ ≤ 1 / (1 + κ) := one_div_le_one_div_of_le hden (by linarith)

theorem reciprocal_cap {κ b : ℝ} (hden : 0 < 1 + κ) (hκ : κ ≤ b) :
    1 / (1 + b) ≤ 1 / (1 + κ) :=
  one_div_le_one_div_of_le hden (by linarith)

theorem pair_exp_split {κ δ u : ℝ} (hgap : 1 / 2 + δ ≤ 1 / (1 + κ)) :
    Real.exp (-(u^2) / (1 + κ)) ≤ Real.exp (-(u^2) / 2) * Real.exp (-δ * u^2) := by
  have h := mul_le_mul_of_nonneg_left hgap (sq_nonneg u)
  rw [← Real.exp_add, Real.exp_le_exp]
  calc
    -(u^2) / (1 + κ) = -(u^2 * (1 / (1 + κ))) := by ring
    _ ≤ -(u^2 * (1 / 2 + δ)) := neg_le_neg h
    _ = -(u^2) / 2 + -δ * u^2 := by ring

theorem pair_exp_near_lag {κ τ u a : ℝ} {m : ℕ}
    (hu : 0 < u) (hτ : τ = (m : ℝ) * a / u) (hden : 0 < 1 + κ)
    (hκ : κ ≤ 1 - 4 * τ^2) :
    Real.exp (-(u^2) / (1 + κ)) ≤
       Real.exp (-(u^2) / 2) * Real.exp (-(a^2 * (m : ℝ)^2)) := by
  have hp := pair_exp_split (u := u) (reciprocal_near hden hκ)
  have hsq : -τ^2 * u^2 = -(a^2 * (m : ℝ)^2) := by
    rw [hτ]
    field_simp
  rw [hsq] at hp
  exact hp

theorem four_region_budget {S p₁ p₂ p₃ p₄ : ℝ}
    (h₁ : p₁ ≤ S / 4) (h₂ : p₂ ≤ S / 12)
    (h₃ : p₃ ≤ S / 12) (h₄ : p₄ ≤ S / 12) :
    p₁ + p₂ + p₃ + p₄ ≤ S / 2 := by linarith

end CenteredCube.RudinDensity

#print axioms CenteredCube.RudinDensity.reciprocal_near
#print axioms CenteredCube.RudinDensity.pair_exp_near_lag
#print axioms CenteredCube.RudinDensity.four_region_budget
