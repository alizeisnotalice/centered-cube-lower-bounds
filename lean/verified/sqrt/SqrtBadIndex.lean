import Mathlib.Data.Sym.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Prod

open scoped BigOperators
open Classical

namespace CenteredCubeSqrt
set_option synthInstance.maxSize 512
set_option synthInstance.maxHeartbeats 50000

abbrev NonzeroBinary (b : ℕ) := {a : Fin b → Bool // a ≠ fun _ => false}
abbrev UnequalLabels (b : ℕ) := {a : NonzeroBinary b × NonzeroBinary b // a.1 ≠ a.2}
abbrev ProductCollision (b : ℕ) := {s : Sym2 (Sym2 (NonzeroBinary b)) // ¬s.IsDiag}
abbrev NeighborCollision (b : ℕ) := UnequalLabels b × UnequalLabels b
abbrev ShortShift (b : ℕ) := UnequalLabels b × Fin 4

abbrev BadIndex (b : ℕ) :=
  NonzeroBinary b ⊕ (ProductCollision b ⊕ (NeighborCollision b ⊕ ShortShift b))

noncomputable instance badIndexFintype (b : ℕ) : Fintype (BadIndex b) :=
  @instFintypeSum _ _ inferInstance
    (@instFintypeSum _ _ inferInstance
      (@instFintypeSum _ _ inferInstance inferInstance))

theorem nonzeroBinary_has_true {b : ℕ} (a : NonzeroBinary b) : ∃ i, a.1 i = true := by
  by_contra hn
  apply a.2
  funext i
  cases h : a.1 i
  · rfl
  · exact False.elim (hn ⟨i,h⟩)

theorem nonzeroBinary_card (b : ℕ) : Fintype.card (NonzeroBinary b) = 2^b-1 := by
  rw [Fintype.card_subtype_compl]
  simp

theorem unequalLabels_card (b : ℕ) :
    Fintype.card (UnequalLabels b) = (2^b-1)*(2^b-2) := by
  have h : (Finset.univ : Finset (NonzeroBinary b)).offDiag =
      Finset.univ.filter (fun x : NonzeroBinary b × NonzeroBinary b => x.1 ≠ x.2) := by
    ext p
    simp
  rw [Fintype.card_subtype, ← h, Finset.offDiag_card, Finset.card_univ,
    nonzeroBinary_card, ← Nat.mul_sub_one]
  rw [show 2 ^ b - 1 - 1 = 2 ^ b - 2 by omega]

theorem productCollision_card (b : ℕ) :
    Fintype.card (ProductCollision b) = ((2^b).choose 2).choose 2 := by
  rw [Sym2.card_subtype_not_diag, Sym2.card, nonzeroBinary_card,
    Nat.sub_add_cancel (Nat.one_le_two_pow)]

def manuscriptBadDegree {b : ℕ} : BadIndex b → ℕ
  | .inl _ => 1
  | .inr (.inl _) => 2
  | .inr (.inr (.inl _)) => 2
  | .inr (.inr (.inr _)) => 1

/-- Exact bad-event budget from the original four index families. -/
theorem manuscriptBadDegree_sum (b : ℕ) :
    (∑ i : BadIndex b, manuscriptBadDegree i) =
      let B := 2^b
      let N := B-1
      let T := B.choose 2
      let R := N*(B-2)
      N + 2*(T.choose 2)+2*R^2+4*R := by
  simp only [Fintype.sum_sum_type, manuscriptBadDegree, Finset.sum_const,
    Finset.card_univ, Nat.nsmul_eq_mul, mul_one, nonzeroBinary_card,
    productCollision_card, Fintype.card_prod, Fintype.card_fin, unequalLabels_card]
  rw [pow_two]
  ac_rfl

#print axioms nonzeroBinary_card
#print axioms unequalLabels_card
#print axioms productCollision_card
#print axioms manuscriptBadDegree_sum

end CenteredCubeSqrt
