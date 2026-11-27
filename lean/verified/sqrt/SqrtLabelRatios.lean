import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.Ring

namespace CenteredCubeSqrt

variable {F : Type*} [Field F]

/-- Multiplicative Sidon condition on the nonzero labels, including repeated factors. -/
def MultiplicativeSidon (W : Set F) : Prop :=
  ∀ ⦃a b c d : F⦄, a ∈ W → b ∈ W → c ∈ W → d ∈ W → a*b = c*d →
    (a = c ∧ b = d) ∨ (a = d ∧ b = c)

/-- A nontrivial ratio has precisely one ordered representation in a Sidon set. -/
theorem nontrivial_ratio_pair_unique {W : Set F} (hW : MultiplicativeSidon W)
    {a b c d : F} (ha : a ∈ W) (hb : b ∈ W) (hc : c ∈ W) (hd : d ∈ W)
    (hab : a ≠ b) (hb0 : b ≠ 0) (hd0 : d ≠ 0) (h : a/b = c/d) :
    a = c ∧ b = d := by
  have e : a*d = c*b := (div_eq_div_iff hb0 hd0).mp h
  rcases hW ha hd hc hb e with good | bad
  · exact ⟨good.1, good.2.symm⟩
  · exact False.elim (hab bad.1)

/-- The collision argument for the intersection of the label space and its nonidentity translate:
any two nonzero intersection elements have the same denominator and hence coincide. -/
theorem translate_intersection_nonzero_unique {W : Set F} (hW : MultiplicativeSidon W)
    {g a b c d : F} (hg : g ≠ 1) (ha : a ∈ W) (hb : b ∈ W)
    (hc : c ∈ W) (hd : d ∈ W) (hb0 : b ≠ 0) (hd0 : d ≠ 0)
    (eab : a = g*b) (ecd : c = g*d) : a = c ∧ b = d := by
  have hne : a ≠ b := by
    intro h
    apply hg
    apply mul_right_cancel₀ hb0
    rw [one_mul, ← eab, h]
  refine nontrivial_ratio_pair_unique hW ha hb hc hd hne hb0 hd0 ?_
  exact (div_eq_div_iff hb0 hd0).mpr (by rw [eab, ecd]; ring)

/-- Nonzero shifts outside the defect set give no nonzero intersection. -/
theorem no_intersection_outside_ratio_set {W : Set F} {g a b : F} (hg : g ≠ 1)
    (ha : a ∈ W) (hb : b ∈ W) (hb0 : b ≠ 0) (e : a = g*b)
    (h : ¬ ∃ x ∈ W, ∃ y ∈ W, x ≠ y ∧ x/y = g) : False := by
  apply h
  refine ⟨a, ha, b, hb, ?_, ?_⟩
  · intro same
    apply hg
    apply mul_right_cancel₀ hb0
    rw [one_mul, ← e, same]
  · exact (div_eq_iff hb0).mpr e

#print axioms nontrivial_ratio_pair_unique
#print axioms translate_intersection_nonzero_unique
#print axioms no_intersection_outside_ratio_set

end CenteredCubeSqrt
