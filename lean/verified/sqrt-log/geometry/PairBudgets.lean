import PairTotals
import ScalePairs
import LagCutoff
import PairExponents

namespace CenteredCube.RudinDensity

open Finset

theorem sum_near_lag_mass (s : Finset ℕ) (M : ℕ) {a B : ℝ}
    (hs : ∀ m ∈ s, 1 ≤ m) (ha : 0 < a) (hB : 0 ≤ B) :
    ∑ m ∈ s, ((M - m : ℕ) : ℝ) * (B * Real.exp (-(a^2 * (m : ℝ)^2))) ≤
      (M : ℝ) * B / (Real.exp (a^2) - 1) := by
  calc
    _ ≤ ∑ m ∈ s, (M : ℝ) * B * Real.exp (-(a^2 * (m : ℝ)^2)) := by
      apply Finset.sum_le_sum
      intro m _
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le M m) (by positivity)
    _ = ((M : ℝ) * B) * ∑ m ∈ s, Real.exp (-(a^2 * (m : ℝ)^2)) := by
      rw [Finset.mul_sum]
    _ ≤ _ := by
      rw [div_eq_mul_inv]
      simpa [one_div] using
        (mul_le_mul_of_nonneg_left (sum_gaussian_lags_le s hs ha)
          (show 0 ≤ (M : ℝ) * B by positivity))

theorem sum_far_pairs_le (M : ℕ) (s : Finset (ℕ × ℕ))
    (hsub : s ⊆ forwardPairs M) (P : ℕ × ℕ → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ p ∈ s, P p ≤ B) :
    ∑ p ∈ s, P p ≤ ((M : ℝ)^2 / 2) * B := by
  have hc : (s.card : ℝ) ≤ ((forwardPairs M).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  calc
    _ ≤ ∑ _p ∈ s, B := Finset.sum_le_sum h
    _ = (s.card : ℝ) * B := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (hc.trans (forwardPairs_card_bound M)) hB

end CenteredCube.RudinDensity

#print axioms CenteredCube.RudinDensity.sum_near_lag_mass
#print axioms CenteredCube.RudinDensity.sum_far_pairs_le
