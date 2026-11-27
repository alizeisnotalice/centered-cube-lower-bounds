import SqrtFiniteField

open scoped BigOperators

namespace CenteredCubeSqrt

open MvPolynomial

/-- Every binary label indexes the exact linear polynomial from papersidon. -/
noncomputable def labelForm {b : ℕ} {F : Type*} [Field F] (a : Fin b → Bool) :
    MvPolynomial (Fin b) F := ∑ i, if a i then X i else 0

theorem eval_label_form {b : ℕ} {F : Type*} [Field F]
    (a : Fin b → Bool) (t : Fin b → F) :
    eval t (labelForm a) = ∑ i, if a i then t i else 0 := by
  classical
  unfold labelForm
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  split <;> simp_all

theorem eval_label_coordinate {b : ℕ} {F : Type*} [Field F]
    (a : Fin b → Bool) (i : Fin b) :
    eval (fun j => if j=i then (1:F) else 0) (labelForm a) =
      if a i then 1 else 0 := by
  rw [eval_label_form]
  trans (if a i then (if i=i then (1:F) else 0) else 0)
  · apply Finset.sum_eq_single i
    · intro j _ hj
      simp [hj]
    · simp
  · simp

theorem labelForm_ne_zero {b : ℕ} {F : Type*} [Field F] {a : Fin b → Bool}
    (ha : ∃ i, a i = true) : (labelForm a : MvPolynomial (Fin b) F) ≠ 0 := by
  obtain ⟨i,hi⟩ := ha
  intro h
  have he := eval_label_coordinate (F:=F) a i
  rw [h] at he
  simp [hi] at he

/-- For each forbidden scalar (g^j
e1), a single coordinate
certifies that the short-displacement polynomial cannot vanish identically. -/
theorem labelForm_short_shift_ne_zero {b : ℕ} {F : Type*} [Field F]
    {a c : Fin b → Bool} (ha : ∃ i, a i = true) {g : F} (hg : g ≠ 1) :
    labelForm a - C g * labelForm c ≠ 0 := by
  obtain ⟨i,hi⟩ := ha
  intro h
  have e := congrArg (eval (fun j : Fin b => if j=i then (1:F) else 0)) h
  simp only [map_sub, map_mul, eval_C, map_zero, eval_label_coordinate, hi, ite_true, sub_eq_zero] at e
  cases hc : c i <;> simp [hc, hg.symm] at e

theorem labelForm_totalDegree_le_one {b : ℕ} {F : Type*} [Field F]
    (a : Fin b → Bool) : (labelForm (F:=F) a).totalDegree ≤ 1 := by
  classical
  unfold labelForm
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun i _ => ?_)
  cases h : a i <;> simp

#print axioms eval_label_coordinate
#print axioms labelForm_ne_zero
#print axioms labelForm_short_shift_ne_zero
#print axioms labelForm_totalDegree_le_one

end CenteredCubeSqrt
