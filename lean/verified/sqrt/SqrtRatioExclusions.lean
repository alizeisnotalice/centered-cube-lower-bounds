import SqrtRatioCount
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

namespace CenteredCubeSqrt

open MvPolynomial
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem labelRatioSet_one_notMem {b d : ℕ} (t : Fin b → LabelField d) :
    (1:LabelField d) ∉ labelRatioSet t := by
  rintro ⟨a,_,c,_,_,hc,hne,hr⟩
  exact hne (by simpa only [one_mul] using (div_eq_iff hc).mp hr)

theorem labelRatioSet_no_neighbor {b d : ℕ} {t : Fin b → LabelField d} {g : LabelField d}
    (h0 : ∀ a, labelValue t a ≠ 0)
    (hp : Function.Injective (fun z : Sym2 (NonzeroBinary b) => eval t (symLabelProduct z)))
    (he : ∀ p q : UnequalLabels b,
      labelValue t p.1.1 * labelValue t q.1.2 ≠
      g * (labelValue t p.1.2 * labelValue t q.1.1))
    {x : LabelField d} (hx : x ∈ labelRatioSet t) : g*x ∉ labelRatioSet t := by
  rw [labelRatioSet_eq_range h0 (labelValue_injective_of_products hp)] at hx ⊢
  obtain ⟨q,rfl⟩ := hx
  rintro ⟨p,h⟩
  apply he p q
  unfold labelRatio at h
  field_simp [h0] at h
  linear_combination h

theorem labelRatioSet_excludes_short {b d : ℕ} {t : Fin b → LabelField d}
    {g : (LabelField d)ˣ}
    (h0 : ∀ a, labelValue t a ≠ 0)
    (hp : Function.Injective (fun z : Sym2 (NonzeroBinary b) => eval t (symLabelProduct z)))
    (hshort : ∀ (p : UnequalLabels b) (j : Fin 4),
      labelValue t p.1.1 ≠ manuscriptShortShifts g j * labelValue t p.1.2)
    (j : Fin 4) : manuscriptShortShifts g j ∉ labelRatioSet t := by
  rw [labelRatioSet_eq_range h0 (labelValue_injective_of_products hp)]
  rintro ⟨p,h⟩
  exact hshort p j ((div_eq_iff (h0 _)).mp h)

#print axioms labelRatioSet_one_notMem
#print axioms labelRatioSet_no_neighbor
#print axioms labelRatioSet_excludes_short

end CenteredCubeSqrt
