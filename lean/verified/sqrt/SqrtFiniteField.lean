import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Subgroup

namespace CenteredCubeSqrt

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- The actual characteristic-two field used in the manuscript. -/
abbrev LabelField (d : ℕ) := GaloisField 2 d

theorem labelField_card {d : ℕ} (hd : 0 < d) :
    Nat.card (LabelField d) = 2^d :=
  GaloisField.card 2 d hd.ne'

theorem labelField_generator {d : ℕ} (hd : 0 < d) :
    ∃ g : (LabelField d)ˣ, orderOf g = 2^d-1 := by
  have cyc : IsCyclic (LabelField d)ˣ := inferInstance
  obtain ⟨g,h⟩ := isCyclic_iff_exists_orderOf_eq_natCard.mp cyc
  exact ⟨g, by rw [h, Nat.card_units, labelField_card hd]⟩

/-- Explicit access to the manuscript's finite polynomial zero-probability budget. -/
theorem label_polynomial_zero_budget {b : ℕ} {F : Type*} [Field F] [Fintype F]
    [DecidableEq F] {p : MvPolynomial (Fin b) F} (hp : p ≠ 0) :
    ((Finset.univ.filter fun f : Fin b → F => MvPolynomial.eval f p = 0).card : ℚ≥0) /
      ((Fintype.card F : ℚ≥0)^b) ≤
      (p.totalDegree : ℚ≥0) / (Fintype.card F : ℚ≥0) := by
  simpa using MvPolynomial.schwartz_zippel_totalDegree hp (Finset.univ : Finset F)

#print axioms labelField_card
#print axioms labelField_generator
#print axioms label_polynomial_zero_budget

end CenteredCubeSqrt
