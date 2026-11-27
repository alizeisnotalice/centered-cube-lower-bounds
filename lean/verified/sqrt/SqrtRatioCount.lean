import SqrtOverlapRank
import Mathlib.Data.Set.Card

namespace CenteredCubeSqrt

open MvPolynomial
open Classical

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem labelValue_injective_of_products {b d : ℕ} {t : Fin b → LabelField d}
    (h : Function.Injective (fun z : Sym2 (NonzeroBinary b) => eval t (symLabelProduct z))) :
    Function.Injective (labelValue t) := by
  intro a c e
  have hh : s(a,a) = s(c,c) := h (by
    simp only [symLabelProduct_mk, map_mul]
    change labelValue t a * labelValue t a = labelValue t c * labelValue t c
    rw [e])
  rcases (Sym2.mk_eq_mk_iff (p:=(a,a)) (q:=(c,c))).mp hh with he | he
  · exact congrArg Prod.fst he
  · exact congrArg Prod.fst he

noncomputable def labelRatio {b d : ℕ} (t : Fin b → LabelField d)
    (p : UnequalLabels b) : LabelField d :=
  labelValue t p.1.1 / labelValue t p.1.2

theorem labelRatioSet_eq_range {b d : ℕ} {t : Fin b → LabelField d}
    (h0 : ∀ a, labelValue t a ≠ 0) (hi : Function.Injective (labelValue t)) :
    labelRatioSet t = Set.range (labelRatio t) := by
  ext g
  constructor
  · rintro ⟨x,hx,c,hc,hx0,hc0,hxc,hr⟩
    obtain ⟨a,ha⟩ := labelSpace_nonzero_is_labelValue t hx hx0
    obtain ⟨e,he⟩ := labelSpace_nonzero_is_labelValue t hc hc0
    have hne : a ≠ e := by
      intro h
      apply hxc
      rw [← ha, ← he, h]
    exact ⟨⟨(a,e),hne⟩, by simpa [labelRatio,ha,he] using hr⟩
  · rintro ⟨p,rfl⟩
    exact ⟨labelValue t p.1.1, labelValue_mem_labelSpace t p.1.1,
      labelValue t p.1.2, labelValue_mem_labelSpace t p.1.2,
      h0 _,h0 _,fun e => p.2 (hi e),rfl⟩

theorem labelRatio_injective {b d : ℕ} {t : Fin b → LabelField d}
    (h0 : ∀ a, labelValue t a ≠ 0)
    (hp : Function.Injective (fun z : Sym2 (NonzeroBinary b) => eval t (symLabelProduct z))) :
    Function.Injective (labelRatio t) := by
  intro p q e
  have hi := labelValue_injective_of_products hp
  have hS := actual_labelSpace_Sidon hp
  have := nontrivial_ratio_pair_unique hS
    ⟨labelValue_mem_labelSpace t p.1.1, h0 _⟩
    ⟨labelValue_mem_labelSpace t p.1.2, h0 _⟩
    ⟨labelValue_mem_labelSpace t q.1.1, h0 _⟩
    ⟨labelValue_mem_labelSpace t q.1.2, h0 _⟩
    (fun h => p.2 (hi h)) (h0 _) (h0 _) e
  exact Subtype.ext (Prod.ext (hi this.1) (hi this.2))

/-- Exact number of distinct nonidentity defect ratios. -/
theorem labelRatioSet_ncard {b d : ℕ} {t : Fin b → LabelField d}
    (h0 : ∀ a, labelValue t a ≠ 0)
    (hp : Function.Injective (fun z : Sym2 (NonzeroBinary b) => eval t (symLabelProduct z))) :
    (labelRatioSet t).ncard = (2^b-1)*(2^b-2) := by
  rw [labelRatioSet_eq_range h0 (labelValue_injective_of_products hp),
    Set.ncard_range_of_injective (labelRatio_injective h0 hp), Nat.card_eq_fintype_card,
    unequalLabels_card]

#print axioms labelRatioSet_ncard
#print axioms labelRatio_injective

end CenteredCubeSqrt
