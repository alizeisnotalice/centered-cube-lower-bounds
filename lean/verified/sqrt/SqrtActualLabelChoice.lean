import SqrtQualifiedLabels
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.LinearAlgebra.LinearIndependent.Defs

namespace CenteredCubeSqrt

open MvPolynomial
open scoped BigOperators

set_option synthInstance.maxSize 512

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- Exact list of the four short displacements (+1,-1,+2,-2). -/
def manuscriptShortShifts {F : Type*} [Field F] (g : Fˣ) : Fin 4 → F :=
  ![(g:F), ((g⁻¹ : Fˣ):F), ((g^2 : Fˣ):F), (((g^2)⁻¹ : Fˣ):F)]

theorem manuscriptShortShifts_ne_one {F : Type*} [Field F] {g : Fˣ}
    (h : 2 < orderOf g) (j : Fin 4) : manuscriptShortShifts g j ≠ 1 := by
  have hn : g ≠ 1 := fun e => by
    subst g
    simp at h
  have hn2 : g^2 ≠ 1 := fun e => by
    have := orderOf_le_of_pow_eq_one (by decide : (0:ℕ)<2) e
    omega
  have hn' : (g:F) ≠ 1 := fun e => hn (Units.ext e)
  have hn2' : ((g^2 : Fˣ):F) ≠ 1 := fun e => hn2 (Units.ext e)
  fin_cases j
  · exact hn'
  · intro e
    exact hn (inv_eq_one.mp (Units.ext e))
  · exact hn2'
  · intro e
    exact hn2 (inv_eq_one.mp (Units.ext e))

/-- The manuscript's actual characteristic-two field and primitive element
satisfy the full simultaneous polynomial exclusion, at the exact H(B) budget. -/
theorem actual_manuscript_label_choice {b d : ℕ} (hd : 0 < d)
    (horder : 2 < 2^d-1)
    (hbudget : labelBudget (2^b) < (2:ℝ)^d) :
    ∃ g : (LabelField d)ˣ, orderOf g = 2^d-1 ∧
      ∃ t : Fin b → LabelField d, ∀ i : BadIndex b,
        eval t (manuscriptBadPolynomial (g:LabelField d) (manuscriptShortShifts g) i) ≠ 0 := by
  classical
  obtain ⟨g,hg⟩ := labelField_generator hd
  let : Fintype (LabelField d) := Fintype.ofFinite _
  have hcard : Fintype.card (LabelField d) = 2^d := by
    rw [← Nat.card_eq_fintype_card, labelField_card hd]
  have h2 : (2 : LabelField d) = 0 := CharP.cast_eq_zero _ _
  rw [← hg] at horder
  refine ⟨g,hg, exists_manuscript_label_vector h2 (Units.ne_zero g) ?_ 
    (manuscriptShortShifts_ne_one horder) ?_⟩
  · exact manuscriptShortShifts_ne_one horder 0
  · rw [hcard]
    exact_mod_cast hbudget

/-- Avoiding each nonzero binary form is exactly the required linear
independence over the prime subfield. -/
theorem actual_label_linearIndependent {b d : ℕ} {t : Fin b → LabelField d}
    (h : ∀ a : NonzeroBinary b, labelValue t a ≠ 0) :
    LinearIndependent (ZMod 2) t := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  by_contra hi
  let a : Fin b → Bool := fun j => decide (c j ≠ 0)
  have hai : a i = true := by simp [a,hi]
  have ha : a ≠ fun _ => false := by
    intro e
    rw [e] at hai
    cases hai
  apply h ⟨a,ha⟩
  unfold labelValue
  rw [eval_label_form]
  convert hc using 1
  apply Finset.sum_congr rfl
  intro j _
  have hjcases : c j = 0 ∨ c j = 1 := by
    generalize hj : c j = z
    fin_cases z
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases hjcases with h0 | h1
  · simp [a,h0]
  · simp [a,h1]

/-- The hypotheses in papersidon alone imply a primitive element and a
linearly independent vector satisfying the exact manuscript exclusions. -/
theorem actual_manuscript_qualified_labels {b d : ℕ} (hb : 2 ≤ b)
    (hbudget : labelBudget (2^b) < (2:ℝ)^d) :
    ∃ g : (LabelField d)ˣ, orderOf g = 2^d-1 ∧
      ∃ t : Fin b → LabelField d, LinearIndependent (ZMod 2) t ∧
        (∀ a, labelValue t a ≠ 0) ∧
        Function.Injective (fun z : Sym2 (NonzeroBinary b) => eval t (symLabelProduct z)) ∧
        (∀ p q : UnequalLabels b,
          labelValue t p.1.1 * labelValue t q.1.2 ≠
            (g:LabelField d) * (labelValue t p.1.2 * labelValue t q.1.1)) ∧
        (∀ (p : UnequalLabels b) (j : Fin 4),
          labelValue t p.1.1 ≠ manuscriptShortShifts g j * labelValue t p.1.2) := by
  have hB : 4 ≤ (2:ℕ)^b := Nat.pow_le_pow_right (show (0:ℕ) < 2 by decide) hb
  have hs : 2^b-1 ≤ ∑ i : BadIndex b, manuscriptBadDegree i := by
    rw [manuscriptBadDegree_sum]
    simp only
    omega
  have hs' : (∑ i : BadIndex b, manuscriptBadDegree i) < (2:ℕ)^d := by
    exact_mod_cast (manuscriptBadDegree_sum_eq_real b).trans_lt hbudget
  have hq : 2 < (2:ℕ)^d-1 := by omega
  have hd : 0 < d := by
    by_contra hn
    have d0 : d = 0 := by omega
    simp [d0] at hq
  obtain ⟨g,hg,t,ht⟩ := actual_manuscript_label_choice hd hq hbudget
  have hv := label_vector_values ht
  exact ⟨g,hg,t,actual_label_linearIndependent hv.1,hv⟩

#print axioms actual_manuscript_qualified_labels

#print axioms actual_label_linearIndependent

#print axioms manuscriptShortShifts_ne_one
#print axioms actual_manuscript_label_choice

end CenteredCubeSqrt
