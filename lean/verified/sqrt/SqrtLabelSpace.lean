import SqrtActualLabelChoice
import SqrtLabelRatios
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

namespace CenteredCubeSqrt

open MvPolynomial
open scoped BigOperators

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem zmod_two_zero_or_one (z : ZMod 2) : z=0 ∨ z=1 := by
  fin_cases z
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- The actual label subspace of the field. -/
noncomputable def labelSpace {b d : ℕ} (t : Fin b → LabelField d) :
    Submodule (ZMod 2) (LabelField d) :=
  Submodule.span (ZMod 2) (Set.range t)

/-- Every label value lies in the manuscript's span. -/
theorem labelValue_mem_labelSpace {b d : ℕ} (t : Fin b → LabelField d) (a : NonzeroBinary b) :
    labelValue t a ∈ labelSpace t := by
  classical
  unfold labelSpace labelValue
  rw [eval_label_form]
  apply (Submodule.mem_span_range_iff_exists_fun (ZMod 2)).mpr
  refine ⟨fun j => if a.1 j then 1 else 0, Finset.sum_congr rfl ?_⟩
  intro j _
  split <;> simp_all

/-- Every nonzero vector in W is the value of a nonzero binary label. -/
theorem labelSpace_nonzero_is_labelValue {b d : ℕ} (t : Fin b → LabelField d)
    {x : LabelField d} (h : x ∈ labelSpace t) (hx : x ≠ 0) :
    ∃ a : NonzeroBinary b, labelValue t a = x := by
  classical
  obtain ⟨c,hc⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod 2)).mp h
  let a : Fin b → Bool := fun i => decide (c i ≠ 0)
  have ha : a ≠ fun _ => false := by
    intro e
    apply hx
    rw [← hc]
    apply Finset.sum_eq_zero
    intro i _
    have hf : a i = false := congrFun e i
    have h0 : c i = 0 := by simpa [a] using hf
    simp [h0]
  refine ⟨⟨a,ha⟩, ?_⟩
  unfold labelValue
  rw [eval_label_form, ← hc]
  apply Finset.sum_congr rfl
  intro j _
  rcases zmod_two_zero_or_one (c j) with h0 | h1
  · simp [a,h0]
  · simp [a,h1]

/-- Distinct unordered nonzero products are the multiplicative Sidon property
on the actual nonzero vectors of the label subspace. -/
theorem actual_labelSpace_Sidon {b d : ℕ} {t : Fin b → LabelField d}
    (h : Function.Injective (fun z : Sym2 (NonzeroBinary b) => eval t (symLabelProduct z))) :
    MultiplicativeSidon {x : LabelField d | x ∈ labelSpace t ∧ x ≠ 0} := by
  intro x y z w hx hy hz hw hprod
  obtain ⟨a,ha⟩ := labelSpace_nonzero_is_labelValue t hx.1 hx.2
  obtain ⟨c,hc⟩ := labelSpace_nonzero_is_labelValue t hy.1 hy.2
  obtain ⟨e,he⟩ := labelSpace_nonzero_is_labelValue t hz.1 hz.2
  obtain ⟨f,hf⟩ := labelSpace_nonzero_is_labelValue t hw.1 hw.2
  have eq : s(a,c) = s(e,f) := h (by
    simp only [symLabelProduct_mk, map_mul]
    change labelValue t a * labelValue t c = labelValue t e * labelValue t f
    rwa [ha,hc,he,hf])
  rcases (Sym2.mk_eq_mk_iff (p:=(a,c)) (q:=(e,f))).mp eq with h1 | h2
  · exact Or.inl ⟨ha.symm.trans ((congrArg (labelValue t) (congrArg Prod.fst h1)).trans he),
      hc.symm.trans ((congrArg (labelValue t) (congrArg Prod.snd h1)).trans hf)⟩
  · exact Or.inr ⟨ha.symm.trans ((congrArg (labelValue t) (congrArg Prod.fst h2)).trans hf),
      hc.symm.trans ((congrArg (labelValue t) (congrArg Prod.snd h2)).trans he)⟩

#print axioms labelValue_mem_labelSpace
#print axioms labelSpace_nonzero_is_labelValue
#print axioms actual_labelSpace_Sidon

end CenteredCubeSqrt
