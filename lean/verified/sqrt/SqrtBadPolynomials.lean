import SqrtBadIndex
import SqrtLabelAvoidance
import SqrtLabelNeighbor
import SqrtLabelSidonPolynomial
import Mathlib.Algebra.MvPolynomial.CommRing

namespace CenteredCubeSqrt

open MvPolynomial
open scoped BigOperators
open Classical

set_option maxHeartbeats 1800000
set_option synthInstance.maxSize 512

variable {b : ℕ} {F : Type*} [Field F]

noncomputable def symLabelProduct (z : Sym2 (NonzeroBinary b)) : MvPolynomial (Fin b) F :=
  (@Sym2.lift (NonzeroBinary b) (MvPolynomial (Fin b) F))
    ⟨fun a c => labelForm a.1 * labelForm c.1,
      fun a c => mul_comm (labelForm a.1) (labelForm c.1)⟩ z

theorem symLabelProduct_mk (a c : NonzeroBinary b) :
    (symLabelProduct s(a,c) : MvPolynomial (Fin b) F) = labelForm a.1 * labelForm c.1 := rfl

theorem symLabelProduct_injective :
    Function.Injective (@symLabelProduct b F _) := by
  intro x y
  refine Sym2.inductionOn₂ x y ?_
  intro a c e f h
  simp only [symLabelProduct_mk] at h
  rcases labelForm_mul_injective_unordered (nonzeroBinary_has_true a) (nonzeroBinary_has_true c)
      (nonzeroBinary_has_true e) (nonzeroBinary_has_true f) h with ⟨h1,h2⟩ | ⟨h1,h2⟩
  · have e1 : a=e := Subtype.ext h1
    have e2 : c=f := Subtype.ext h2
    simp [e1,e2]
  · have e1 : a=f := Subtype.ext h1
    have e2 : c=e := Subtype.ext h2
    simp [e1,e2]

theorem symLabelProduct_degree (p : Sym2 (NonzeroBinary b)) :
    (symLabelProduct (F:=F) p).totalDegree ≤ 2 := by
  refine Sym2.inductionOn p ?_
  intro a c
  rw [symLabelProduct_mk]
  exact (totalDegree_mul _ _).trans
    (Nat.add_le_add (labelForm_totalDegree_le_one a.1) (labelForm_totalDegree_le_one c.1))

noncomputable def manuscriptBadPolynomial (g : F) (short : Fin 4 → F) :
    BadIndex b → MvPolynomial (Fin b) F
  | .inl a => labelForm a.1
  | .inr (.inl x) => symLabelProduct x.1.out.1 - symLabelProduct x.1.out.2
  | .inr (.inr (.inl ⟨p,q⟩)) =>
      labelForm p.1.1.1 * labelForm q.1.2.1 -
        C g * (labelForm p.1.2.1 * labelForm q.1.1.1)
  | .inr (.inr (.inr ⟨p,j⟩)) =>
      labelForm p.1.1.1 - C (short j)*labelForm p.1.2.1

theorem manuscriptBadPolynomial_nonzero (h2 : (2:F)=0)
    {g : F} (hg0 : g ≠ 0) (hg1 : g ≠ 1) {short : Fin 4 → F}
    (hs : ∀ j, short j ≠ 1) (i : BadIndex b) :
    manuscriptBadPolynomial g short i ≠ 0 := by
  rcases i with a | p | ⟨p,q⟩ | ⟨p,j⟩
  · exact labelForm_ne_zero (nonzeroBinary_has_true a)
  · intro h
    have eq := symLabelProduct_injective (F:=F) (sub_eq_zero.mp h)
    exact p.2 (by
      have e := Sym2.mk_fst_out_snd_out p.1
      rw [eq] at e
      rw [← e]
      simp)
  · exact neighbor_ratio_polynomial_ne_zero h2 hg0 hg1 (nonzeroBinary_has_true p.1.2)
      (nonzeroBinary_has_true q.1.1)
  · exact labelForm_short_shift_ne_zero (nonzeroBinary_has_true p.1.1) (hs j)

theorem manuscriptBadPolynomial_degree (g : F) (short : Fin 4 → F) (i : BadIndex b) :
    (manuscriptBadPolynomial g short i).totalDegree ≤ manuscriptBadDegree i := by
  have aux (z : F) (p : MvPolynomial (Fin b) F) :
      (C z*p).totalDegree ≤ p.totalDegree := by
    exact (totalDegree_mul _ _).trans (by simp)
  rcases i with a | p | ⟨p,q⟩ | ⟨p,j⟩
  · exact labelForm_totalDegree_le_one a.1
  · apply (totalDegree_sub _ _).trans
    exact max_le (symLabelProduct_degree (F:=F) _) (symLabelProduct_degree (F:=F) _)
  · apply (totalDegree_sub _ _).trans
    apply max_le
    · exact (totalDegree_mul _ _).trans
        (Nat.add_le_add (labelForm_totalDegree_le_one _) (labelForm_totalDegree_le_one _))
    · exact (aux _ _).trans ((totalDegree_mul _ _).trans
        (Nat.add_le_add (labelForm_totalDegree_le_one _) (labelForm_totalDegree_le_one _)))
  · apply (totalDegree_sub _ _).trans
    exact max_le (labelForm_totalDegree_le_one _) ((aux _ _).trans (labelForm_totalDegree_le_one _))

#print axioms manuscriptBadPolynomial_nonzero
#print axioms manuscriptBadPolynomial_degree

end CenteredCubeSqrt
