import SqrtCyclicDefects

namespace CenteredCubeSqrt

open MvPolynomial
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem cyclic_short_shift_values {d : ℕ} (hd : 0 < d) (g : (LabelField d)ˣ)
    (hg : orderOf g = 2^d-1) :
    (phaseState hd g hg 1 : LabelField d) = manuscriptShortShifts g 0 ∧
    (phaseState hd g hg (-1) : LabelField d) = manuscriptShortShifts g 1 ∧
    (phaseState hd g hg 2 : LabelField d) = manuscriptShortShifts g 2 ∧
    (phaseState hd g hg (-2) : LabelField d) = manuscriptShortShifts g 3 := by
  have e (j : ℤ) :
      (phaseState hd g hg (j : ZMod (2^d-1)) : LabelField d) = ((g^j : (LabelField d)ˣ) : LabelField d) :=
    congrArg Units.val (cyclicStateEquiv_integer hd g hg j)
  constructor
  · change _ = (g : LabelField d)
    simpa only [Int.cast_one, zpow_one] using e 1
  constructor
  · change _ = ((g⁻¹ : (LabelField d)ˣ) : LabelField d)
    simpa only [Int.cast_neg, Int.cast_one, zpow_neg, zpow_one] using e (-1)
  constructor
  · change _ = ((g^2 : (LabelField d)ˣ) : LabelField d)
    simpa only [Int.cast_ofNat, zpow_ofNat] using e 2
  · change _ = (((g^2)⁻¹ : (LabelField d)ˣ) : LabelField d)
    simpa only [Int.cast_neg, Int.cast_ofNat, zpow_neg, zpow_ofNat] using e (-2)

theorem cyclicDefects_short_excluded {b d : ℕ} (hd : 0 < d) (g : (LabelField d)ˣ)
    (hg : orderOf g = 2^d-1) {t : Fin b → LabelField d}
    (h0 : ∀ a, labelValue t a ≠ 0)
    (hp : Function.Injective (fun z : Sym2 (NonzeroBinary b) => eval t (symLabelProduct z)))
    (he : ∀ (p : UnequalLabels b) (j : Fin 4),
      labelValue t p.1.1 ≠ manuscriptShortShifts g j * labelValue t p.1.2) :
    (1 : ZMod (2^d-1)) ∉ cyclicDefects hd g hg t ∧ -1 ∉ cyclicDefects hd g hg t ∧
      2 ∉ cyclicDefects hd g hg t ∧ -2 ∉ cyclicDefects hd g hg t := by
  obtain ⟨h1,hm1,h2,hm2⟩ := cyclic_short_shift_values hd g hg
  unfold cyclicDefects
  simp only [Set.mem_preimage, h1, hm1, h2, hm2]
  exact ⟨labelRatioSet_excludes_short h0 hp he 0, labelRatioSet_excludes_short h0 hp he 1,
    labelRatioSet_excludes_short h0 hp he 2, labelRatioSet_excludes_short h0 hp he 3⟩

/-- The paper's defect set stays non-adjacent after adjoining the zero state. -/
theorem cyclicDefects_zero_union_nonadjacent {b d : ℕ} (hd : 0 < d) (g : (LabelField d)ˣ)
    (hg : orderOf g = 2^d-1) (hord : 2 < orderOf g) {t : Fin b → LabelField d}
    (h0 : ∀ a, labelValue t a ≠ 0)
    (hp : Function.Injective (fun z : Sym2 (NonzeroBinary b) => eval t (symLabelProduct z)))
    (hadj : ∀ p q : UnequalLabels b,
      labelValue t p.1.1 * labelValue t q.1.2 ≠
        (g:LabelField d) * (labelValue t p.1.2 * labelValue t q.1.1))
    (hshort : ∀ (p : UnequalLabels b) (j : Fin 4),
      labelValue t p.1.1 ≠ manuscriptShortShifts g j * labelValue t p.1.2)
    {j : ZMod (2^d-1)} (hj : j ∈ insert 0 (cyclicDefects hd g hg t)) :
    j+1 ∉ insert 0 (cyclicDefects hd g hg t) := by
  obtain ⟨h1,hm1,_,_⟩ := cyclicDefects_short_excluded hd g hg h0 hp hshort
  have h10 : (1 : ZMod (2^d-1)) ≠ 0 := by
    intro e
    have e' := congrArg (fun j : ZMod (2^d-1) => (phaseState hd g hg j : LabelField d)) e
    rw [(cyclic_short_shift_values hd g hg).1,
      show phaseState hd g hg 0=1 from map_one (cyclicStateEquiv hd g hg), Units.val_one] at e'
    exact manuscriptShortShifts_ne_one hord 0 e'
  rcases Set.mem_insert_iff.mp hj with rfl | hj
  · simpa [h10] using h1
  · intro h
    rcases Set.mem_insert_iff.mp h with hz | hD
    · have e : j = -1 := (eq_neg_iff_add_eq_zero).mpr hz
      exact hm1 (e ▸ hj)
    · exact cyclicDefects_step_excluded hd g hg h0 hp hadj hj hD

#print axioms cyclicDefects_short_excluded
#print axioms cyclicDefects_zero_union_nonadjacent

end CenteredCubeSqrt
