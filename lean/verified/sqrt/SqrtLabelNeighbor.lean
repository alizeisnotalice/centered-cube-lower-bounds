import SqrtLabelLinearForms

open scoped BigOperators

namespace CenteredCubeSqrt

open MvPolynomial

variable {b : ℕ} {F : Type*} [Field F]

theorem eval_label_at_binary {a : Fin b → Bool} (h2 : (2:F)=0)
    (t : Fin b → F) (ht : ∀ i, t i = 0 ∨ t i = 1) :
    eval t (labelForm a) = 0 ∨ eval t (labelForm a) = 1 := by
  rw [eval_label_form]
  have hs (s : Finset (Fin b)) : (∑ i ∈ s, if a i then t i else 0) = 0 ∨
      (∑ i ∈ s, if a i then t i else 0) = 1 := by
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      have h11 : (1:F)+1=0 := (one_add_one_eq_two : (1:F)+1=2).trans h2
      have hi' : (if a i then t i else 0)=0 ∨ (if a i then t i else 0)=1 := by
        cases he : a i
        · simp
        · simpa using ht i
      rcases hi' with hc | hc <;> rcases ih with hh | hh <;>
        simp [hc,hh,h11]
  exact hs Finset.univ

/-- Two nonzero binary linear forms can be simultaneously one on a binary
test point. In the disjoint-support case take one coordinate from each. -/
theorem two_label_forms_simultaneously_one
    {a c : Fin b → Bool} (ha : ∃ i, a i = true) (hc : ∃ i, c i = true) :
    ∃ t : Fin b → F, (∀ i, t i = 0 ∨ t i = 1) ∧
      eval t (labelForm a) = 1 ∧ eval t (labelForm c) = 1 := by
  classical
  by_cases h : ∃ i, a i = true ∧ c i = true
  · obtain ⟨i, hai, hci⟩ := h
    refine ⟨fun j => if j=i then 1 else 0, fun j => ?_, ?_, ?_⟩
    · by_cases hj : j=i <;> simp [hj]
    · simp [eval_label_coordinate, hai]
    · simp [eval_label_coordinate, hci]
  · obtain ⟨i, hi⟩ := ha
    obtain ⟨j, hj⟩ := hc
    have hai : a j = false := by
      cases e : a j
      · rfl
      · exact False.elim (h ⟨j,e,hj⟩)
    have hcj : c i = false := by
      cases e : c i
      · rfl
      · exact False.elim (h ⟨i,hi,e⟩)
    let t : Fin b → F := fun k => if k=i ∨ k=j then 1 else 0
    refine ⟨t, fun k => ?_, ?_, ?_⟩
    · by_cases hk : k=i ∨ k=j <;> simp [t,hk]
    · rw [eval_label_form]
      trans (if a i then t i else 0)
      · apply Finset.sum_eq_single i
        · intro k _ hk
          by_cases hkj : k=j
          · simp [hkj, hai]
          · simp [t, hk, hkj]
        · simp
      · simp [t,hi]
    · rw [eval_label_form]
      trans (if c j then t j else 0)
      · apply Finset.sum_eq_single j
        · intro k _ hk
          by_cases hki : k=i
          · simp [hki, hcj]
          · simp [t,hki,hk]
        · simp
      · simp [t,hj]

/-- Exact nonvanishing of the adjacent-ratio polynomial for any nonidentity
nonzero scalar, using evaluation rather than an appeal to informal coefficients. -/
theorem neighbor_ratio_polynomial_ne_zero {a e c f : Fin b → Bool} {g : F}
    (h2 : (2:F)=0) (hg0 : g ≠ 0) (hg1 : g ≠ 1)
    (hc : ∃ i, c i = true) (hf : ∃ i, f i = true) :
    labelForm a * labelForm e - C g * (labelForm c * labelForm f) ≠ 0 := by
  obtain ⟨t,ht,hc',hf'⟩ := two_label_forms_simultaneously_one (F:=F) hc hf
  intro h
  have eq := congrArg (eval t) h
  simp only [map_sub, map_mul, eval_C, hc',hf',mul_one,map_zero,sub_eq_zero] at eq
  rcases eval_label_at_binary (a:=a) h2 t ht with ha | ha <;>
    rcases eval_label_at_binary (a:=e) h2 t ht with he | he <;>
    simp_all [hg0.symm,hg1.symm]

#print axioms eval_label_at_binary
#print axioms two_label_forms_simultaneously_one
#print axioms neighbor_ratio_polynomial_ne_zero

end CenteredCubeSqrt
