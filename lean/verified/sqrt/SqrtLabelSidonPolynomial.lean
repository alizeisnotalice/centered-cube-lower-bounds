import SqrtLabelLinearForms
import Mathlib.Tactic.Ring

open scoped BigOperators

namespace CenteredCubeSqrt

open MvPolynomial

variable {b : ℕ} {F : Type*} [Field F]

theorem eval_label_add (a : Fin b → Bool) (t u : Fin b → F) :
    eval (fun i => t i + u i) (labelForm a) =
      eval t (labelForm a) + eval u (labelForm a) := by
  simp only [eval_label_form, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  split <;> simp_all

theorem eval_label_sub (a : Fin b → Bool) (t u : Fin b → F) :
    eval (fun i => t i - u i) (labelForm a) =
      eval t (labelForm a) - eval u (labelForm a) := by
  simp only [eval_label_form, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  split <;> simp_all

theorem eval_label_scale (a : Fin b → Bool) (r : F) (t : Fin b → F) :
    eval (fun i => r*t i) (labelForm a) = r * eval t (labelForm a) := by
  simp only [eval_label_form, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  split <;> simp_all

/-- Distinct nonzero binary forms cannot be proportional, characterized via their kernels. -/
theorem eq_label_of_kernel_inclusion {a c : Fin b → Bool}
    (ha : ∃ i, a i = true) (hc : ∃ i, c i = true)
    (h : ∀ t : Fin b → F, eval t (labelForm a) = 0 → eval t (labelForm c) = 0) :
    c = a := by
  obtain ⟨i,hi⟩ := ha
  let e : Fin b → F := fun j => if j=i then 1 else 0
  have ea : eval e (labelForm a) = 1 := by simp [e,eval_label_coordinate,hi]
  have eq (t : Fin b → F) :
      eval t (labelForm c) = eval t (labelForm a) * eval e (labelForm c) := by
    have e0 : eval (fun j => t j-(eval t (labelForm a))*e j) (labelForm a) = 0 := by
      rw [eval_label_sub, eval_label_scale, ea, mul_one, sub_self]
    have e1 := h _ e0
    rw [eval_label_sub, eval_label_scale] at e1
    exact sub_eq_zero.mp e1
  have ec : eval e (labelForm c) = 1 := by
    rw [show eval e (labelForm c) = if c i then 1 else 0 from eval_label_coordinate c i]
    cases eci : c i
    · obtain ⟨j,hj⟩ := hc
      let ej : Fin b → F := fun k => if k=j then 1 else 0
      have ec0 : eval e (labelForm c) = 0 := by simp [e,eval_label_coordinate,eci]
      have ecj : eval ej (labelForm c) = 1 := by simp [ej,eval_label_coordinate,hj]
      have contra := eq ej
      rw [ec0,mul_zero,ecj] at contra
      exact False.elim (one_ne_zero contra)
    · simp
  funext j
  let ej : Fin b → F := fun k => if k=j then 1 else 0
  have ejc := eq ej
  rw [ec,mul_one] at ejc
  simp only [ej,eval_label_coordinate] at ejc
  cases hcj : c j <;> cases haj : a j
  · rfl
  · exfalso
    simp [hcj,haj] at ejc
  · exfalso
    simp [hcj,haj] at ejc
  · rfl

/-- An identity of two products of binary linear forms forces exactly the
two unordered equality options needed in the second bad-event family. -/
theorem labelForm_mul_injective_unordered {a c e f : Fin b → Bool}
    (ha : ∃ i, a i = true) (hc : ∃ i, c i = true)
    (he : ∃ i, e i = true) (hf : ∃ i, f i = true)
    (h : (labelForm a : MvPolynomial (Fin b) F)*labelForm c = labelForm e*labelForm f) :
    (a=e ∧ c=f) ∨ (a=f ∧ c=e) := by
  have van (t : Fin b → F) (ht : eval t (labelForm a)=0) :
      eval t (labelForm e)=0 ∨ eval t (labelForm f)=0 := by
    have eq := congrArg (eval t) h
    rw [map_mul,map_mul,ht,zero_mul] at eq
    exact mul_eq_zero.mp eq.symm
  by_cases ke : ∀ t : Fin b → F, eval t (labelForm a)=0 → eval t (labelForm e)=0
  · have ae : e = a := eq_label_of_kernel_inclusion ha he ke
    subst e
    have hd : (labelForm c : MvPolynomial (Fin b) F)=labelForm f :=
      mul_left_cancel₀ (labelForm_ne_zero ha) h
    have cf : f=c := eq_label_of_kernel_inclusion hc hf (by rw [hd]; exact fun _ hp => hp)
    exact Or.inl ⟨rfl,cf.symm⟩
  · push Not at ke
    obtain ⟨u,hu,hue⟩ := ke
    have huf : eval u (labelForm f)=0 := (van u hu).resolve_left hue
    have kf (t : Fin b → F) (ht : eval t (labelForm a)=0) : eval t (labelForm f)=0 := by
      by_contra hn
      have hte : eval t (labelForm e)=0 := (van t ht).resolve_right hn
      have hat : eval (fun j => t j+u j) (labelForm a)=0 := by rw [eval_label_add,ht,hu,add_zero]
      rcases van (fun j => t j+u j) hat with heq | hfq
      · rw [eval_label_add,hte,zero_add] at heq
        exact hue heq
      · rw [eval_label_add,huf,add_zero] at hfq
        exact hn hfq
    have af : f=a := eq_label_of_kernel_inclusion ha hf kf
    subst f
    rw [mul_comm (labelForm e) (labelForm a)] at h
    have hd : (labelForm c : MvPolynomial (Fin b) F)=labelForm e :=
      mul_left_cancel₀ (labelForm_ne_zero ha) h
    have ce : e=c := eq_label_of_kernel_inclusion hc he (by rw [hd]; exact fun _ hp => hp)
    exact Or.inr ⟨rfl,ce.symm⟩

#print axioms eq_label_of_kernel_inclusion
#print axioms labelForm_mul_injective_unordered

end CenteredCubeSqrt
