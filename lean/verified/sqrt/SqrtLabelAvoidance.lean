import SqrtFiniteField

open scoped BigOperators

namespace CenteredCubeSqrt

/-- Finite union argument for any family of bad polynomial conditions. The
strict degree budget is in units of one field element, with no probability
measure hypotheses and no replacement of point counts by independence. -/
theorem exists_avoid_polynomial_family {b : ℕ} {F ι : Type*}
    [Field F] [Fintype F] [DecidableEq F] [DecidableEq ι]
    (s : Finset ι) (p : ι → MvPolynomial (Fin b) F)
    (hn : ∀ i ∈ s, p i ≠ 0)
    (hbudget : ∑ i ∈ s, (p i).totalDegree < Fintype.card F) :
    ∃ f : Fin b → F, ∀ i ∈ s, MvPolynomial.eval f (p i) ≠ 0 := by
  classical
  let roots (i : ι) := Finset.univ.filter fun f : Fin b → F => MvPolynomial.eval f (p i) = 0
  let q : ℚ≥0 := Fintype.card F
  have hq : 0 < q := by dsimp [q]; exact_mod_cast Fintype.card_pos
  have hg : 0 < q^b := pow_pos hq _
  have hbudget' : (∑ i ∈ s, ((p i).totalDegree : ℚ≥0)) < q := by
    dsimp only [q]
    exact_mod_cast hbudget
  have hden : ((s.biUnion roots).card : ℚ≥0) ≤ ∑ i ∈ s, ((roots i).card : ℚ≥0) := by
    exact_mod_cast (Finset.card_biUnion_le (s := s) (t := roots))
  have habs : ((s.biUnion roots).card : ℚ≥0) / q^b < 1 := by
    calc
      _ ≤ (∑ i ∈ s, ((roots i).card : ℚ≥0)) / q^b :=
        div_le_div_of_nonneg_right hden hg.le
      _ = ∑ i ∈ s, (((roots i).card : ℚ≥0) / q^b) := Finset.sum_div _ _ _
      _ ≤ ∑ i ∈ s, (((p i).totalDegree : ℚ≥0) / q) :=
        Finset.sum_le_sum fun i hi => label_polynomial_zero_budget (hn i hi)
      _ = (∑ i ∈ s, ((p i).totalDegree : ℚ≥0)) / q := (Finset.sum_div _ _ _).symm
      _ < 1 := (div_lt_iff₀ hq).2 (by simpa using hbudget')
  by_contra! hc
  have he : s.biUnion roots = Finset.univ := by
    ext f
    simp only [Finset.mem_univ, iff_true]
    obtain ⟨i, hi, hif⟩ := hc f
    exact Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hif⟩⟩
  rw [he, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow,
    div_self (ne_of_gt hg)] at habs
  exact (lt_irrefl _ habs)

#print axioms exists_avoid_polynomial_family

end CenteredCubeSqrt
