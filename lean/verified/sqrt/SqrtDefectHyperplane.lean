import SqrtOverlapRank

namespace CenteredCubeSqrt

open scoped BigOperators
open MvPolynomial
open Classical

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- The unique binary compatibility relation for a defective joint trace label. -/
noncomputable def traceMatchForm {b : ℕ} (a c : NonzeroBinary b) :
    LabelOutput b →ₗ[ZMod 2] ZMod 2 :=
  (∑ i : Fin b, if a.1 i then LinearMap.proj (.inl i) else 0) +
  (∑ i : Fin b, if c.1 i then LinearMap.proj (.inr i) else 0)

theorem traceMatchForm_apply {b : ℕ} (a c : NonzeroBinary b) (y : LabelOutput b) :
    traceMatchForm a c y =
      (∑ i, if a.1 i then y (.inl i) else 0) +
      (∑ i, if c.1 i then y (.inr i) else 0) := by
  unfold traceMatchForm
  rw [LinearMap.add_apply, LinearMap.sum_apply, LinearMap.sum_apply]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> split <;> simp_all

theorem traceMatchForm_surj {b : ℕ} (a c : NonzeroBinary b) :
    Function.Surjective (traceMatchForm a c) := by
  obtain ⟨i,hi⟩ := nonzeroBinary_has_true a
  intro y
  refine ⟨fun j => if j=Sum.inl i then y else 0, ?_⟩
  rw [traceMatchForm_apply]
  suffices hu : (∑ j : Fin b, if a.1 j then (if (Sum.inl j : Fin b ⊕ Fin b) = Sum.inl i then y else 0) else 0) = y by
    simpa using hu
  trans (if a.1 i then (if Sum.inl i = (Sum.inl i : Fin b ⊕ Fin b) then y else 0) else 0)
  · apply Finset.sum_eq_single i
    · intro j _ hj
      simp [hj]
    · simp
  · simp [hi]

theorem traceMatchForm_compatible {b d : ℕ} (t : Fin b → LabelField d)
    (g : (LabelField d)ˣ) (a c : NonzeroBinary b)
    (h : labelValue t a = (g:LabelField d)*labelValue t c)
    (x : LabelField d) : traceMatchForm a c (jointTrace t g x)=0 := by
  let Tr := Algebra.trace (ZMod 2) (LabelField d)
  have left : (∑ i : Fin b, if a.1 i then jointTrace t g x (.inl i) else 0) =
      Tr (labelValue t a*x) := by
    rw [labelValue, eval_label_form, Finset.sum_mul, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    split <;> simp_all [jointTrace,jointTraceRows,Tr]
  have right : (∑ i : Fin b, if c.1 i then jointTrace t g x (.inr i) else 0) =
      Tr (((g:LabelField d)*labelValue t c)*x) := by
    rw [labelValue, eval_label_form, Finset.mul_sum, Finset.sum_mul, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    split <;> simp_all [jointTrace,jointTraceRows,Tr]
  rw [traceMatchForm_apply, left,right,h]
  have h2 : (2 : ZMod 2)=0 := CharP.cast_eq_zero _ _
  rw [← two_mul,h2,zero_mul]

/-- An actual deficient image consists of exactly the outputs satisfying
the unique compatibility relation, not a strict subset of that hyperplane. -/
theorem traceDefect_image_hyperplane {b d : ℕ} {t : Fin b → LabelField d}
    (ht : LinearIndependent (ZMod 2) t)
    (g : (LabelField d)ˣ) (a c : NonzeroBinary b)
    (hmatch : labelValue t a = (g:LabelField d)*labelValue t c)
    (hr : Module.finrank (ZMod 2) (traceOverlap t g)=1) :
    (jointTrace t g).range = (traceMatchForm a c).ker := by
  apply Submodule.eq_of_le_of_finrank_le
  · rintro y ⟨x,rfl⟩
    exact traceMatchForm_compatible t g a c hmatch x
  · have h := (traceMatchForm a c).finrank_range_add_finrank_ker
    have htop : (traceMatchForm a c).range = ⊤ := LinearMap.range_eq_top.mpr (traceMatchForm_surj a c)
    rw [htop, finrank_top] at h
    rw [jointTrace_rank ht, hr]
    simp [LabelOutput, two_mul] at h ⊢
    omega

#print axioms traceMatchForm_surj
#print axioms traceMatchForm_compatible
#print axioms traceDefect_image_hyperplane

end CenteredCubeSqrt
