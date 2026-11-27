import SqrtBadPolynomials
import SqrtLabelBudget
import Mathlib.Data.Nat.Choose.Cast

namespace CenteredCubeSqrt

open MvPolynomial
open scoped BigOperators
open Classical

set_option synthInstance.maxSize 512

theorem manuscriptBadDegree_sum_eq_real (b : ℕ) :
    ((∑ i : BadIndex b, manuscriptBadDegree i : ℕ) : ℝ) = labelBudget (2^b) := by
  rw [manuscriptBadDegree_sum]
  dsimp only [labelBudget]
  push_cast
  have hb1 : (1:ℕ) ≤ 2^b := Nat.one_le_two_pow
  have hT : (((2^b : ℕ).choose 2 : ℕ):ℝ) = ((2:ℝ)^b-1)*(((2:ℝ)^b-1)+1)/2 := by
    rw [Nat.cast_choose_two]
    push_cast
    ring
  have hBm (n : ℕ) (hn : n ≤ 2^b) : ((2^b-n:ℕ):ℝ) = (2:ℝ)^b - n := by 
    rw [Nat.cast_sub hn]
    push_cast
    rfl
  by_cases b0 : b=0
  · subst b
    norm_num
  · have hb2 : (2:ℕ) ≤ 2^b := by
      cases b with
      | zero => contradiction
      | succ b =>
        rw [pow_succ]
        exact Nat.le_mul_of_pos_left _ (Nat.one_le_two_pow)
    rw [Nat.cast_choose_two, hT, hBm 1 hb1, hBm 2 hb2]
    ring

/-- Complete exact polynomial avoidance at the manuscript's threshold. This
establishes the finite deterministic choice without probability independence. -/
theorem exists_manuscript_label_vector {b : ℕ} {F : Type*} [Field F] [Fintype F]
    (h2 : (2:F)=0) {g : F} (hg0 : g ≠ 0) (hg1 : g ≠ 1) {short : Fin 4 → F}
    (hs : ∀ j, short j ≠ 1)
    (hbudget : labelBudget (2^b) < Fintype.card F) :
    ∃ t : Fin b → F, ∀ i : BadIndex b, eval t (manuscriptBadPolynomial g short i) ≠ 0 := by
  have hb : (∑ i : BadIndex b, manuscriptBadDegree i) < Fintype.card F := by
    exact_mod_cast ((manuscriptBadDegree_sum_eq_real b).trans_lt hbudget)
  obtain ⟨t, ht⟩ := exists_avoid_polynomial_family (Finset.univ : Finset (BadIndex b))
      (manuscriptBadPolynomial g short) (fun i _ => manuscriptBadPolynomial_nonzero h2 hg0 hg1 hs i)
      ((Finset.sum_le_sum fun i _ => manuscriptBadPolynomial_degree g short i).trans_lt hb)
  exact ⟨t, fun i => ht i (Finset.mem_univ i)⟩

noncomputable def labelValue {b : ℕ} {F : Type*} [Field F] (t : Fin b → F) (a : NonzeroBinary b) : F :=
  eval t (labelForm a.1)

theorem label_vector_values {b : ℕ} {F : Type*} [Field F] {g : F} {short : Fin 4 → F}
    {t : Fin b → F} (ht : ∀ i : BadIndex b, eval t (manuscriptBadPolynomial g short i) ≠ 0) :
    (∀ a, labelValue t a ≠ 0) ∧
    Function.Injective (fun z : Sym2 (NonzeroBinary b) => eval t (symLabelProduct z)) ∧
    (∀ p q : UnequalLabels b,
      labelValue t p.1.1 * labelValue t q.1.2 ≠
        g * (labelValue t p.1.2 * labelValue t q.1.1)) ∧
    (∀ (p : UnequalLabels b) (j : Fin 4),
      labelValue t p.1.1 ≠ short j * labelValue t p.1.2) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a
    exact ht (.inl a)
  · intro p q hpq
    by_contra hn
    have nd : ¬(s(p,q) : Sym2 (Sym2 (NonzeroBinary b))).IsDiag := by simpa using hn
    have nz := ht (.inr (.inl ⟨s(p,q), nd⟩))
    have e := Sym2.mk_fst_out_snd_out (s(p,q) : Sym2 (Sym2 (NonzeroBinary b)))
    have e' := (Sym2.mk_eq_mk_iff (p := (s(p,q) : Sym2 (Sym2 (NonzeroBinary b))).out) (q := (p,q))).mp e
    apply nz
    simp only [manuscriptBadPolynomial, map_sub, sub_eq_zero]
    rcases e' with e' | e'
    · simpa [congrArg Prod.fst e', congrArg Prod.snd e'] using hpq
    · simpa [congrArg Prod.fst e', congrArg Prod.snd e'] using hpq.symm
  · intro p q
    simpa [manuscriptBadPolynomial, eval_C, sub_eq_zero, labelValue] using ht (.inr (.inr (.inl (p,q))))
  · intro p j
    simpa [manuscriptBadPolynomial, eval_C, sub_eq_zero, labelValue] using ht (.inr (.inr (.inr (p,j))))

#print axioms manuscriptBadDegree_sum_eq_real
#print axioms exists_manuscript_label_vector
#print axioms label_vector_values

end CenteredCubeSqrt
