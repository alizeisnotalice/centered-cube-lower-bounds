import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace CenteredCube.RudinDensity

theorem card_lag_subset_of_cutoff (s : Finset ℕ) {a u T : ℝ}
    (ha : 0 < a) (hu : 0 < u) (hT : 0 ≤ T)
    (hs : ∀ m ∈ s, (m : ℝ) * a / u ≤ T) :
    (s.card : ℝ) ≤ T * u / a + 1 := by
  have hnon : 0 ≤ T * u / a := by positivity
  have hsub : s ⊆ Finset.range (⌊T * u / a⌋₊ + 1) := by
    intro m hm
    apply Finset.mem_range.mpr
    apply Nat.lt_succ_of_le
    apply Nat.le_floor
    exact (le_div_iff₀ ha).mpr ((div_le_iff₀ hu).mp (hs m hm))
  have hcard : s.card ≤ ⌊T * u / a⌋₊ + 1 := by
    simpa using Finset.card_le_card hsub
  have hcast : (s.card : ℝ) ≤ (⌊T * u / a⌋₊ : ℝ) + 1 := by
    exact_mod_cast hcard
  linarith [Nat.floor_le hnon]

theorem bounded_lag_mass (s : Finset ℕ) (M : ℕ) {L b : ℝ}
    (hcard : (s.card : ℝ) ≤ L) (hb : 0 ≤ b) :
    ∑ m ∈ s, ((M - m : ℕ) : ℝ) * b ≤ (M : ℝ) * L * b := by
  calc
    _ ≤ ∑ _m ∈ s, (M : ℝ) * b := by
      apply Finset.sum_le_sum
      intro m _
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le M m) hb
    _ = (M : ℝ) * (s.card : ℝ) * b := by
      rw [Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hcard (by positivity)) hb

end CenteredCube.RudinDensity

#print axioms CenteredCube.RudinDensity.card_lag_subset_of_cutoff
#print axioms CenteredCube.RudinDensity.bounded_lag_mass
