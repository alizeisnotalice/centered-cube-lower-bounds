import SqrtFiniteField

namespace CenteredCubeSqrt

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem finite_field_primitive_powers_all {d : ℕ} (hd : 0 < d) {g : (LabelField d)ˣ}
    (hg : orderOf g = 2^d-1) :
    ∀ x : (LabelField d)ˣ, x ∈ Subgroup.zpowers g := by
  have hcard : orderOf g = Nat.card (LabelField d)ˣ := by
    rw [Nat.card_units, labelField_card hd, hg]
  have e : Subgroup.zpowers g = ⊤ := by
    rwa [← Subgroup.card_eq_iff_eq_top, Nat.card_zpowers]
  intro x
  rw [e]
  trivial

/-- The literal period (jmapsto g^j) traverses all nonzero field states. -/
noncomputable def cyclicStateEquiv {d : ℕ} (hd : 0 < d) (g : (LabelField d)ˣ)
    (hg : orderOf g = 2^d-1) :
    Multiplicative (ZMod (2^d-1)) ≃* (LabelField d)ˣ :=
  zmodMulEquivOfGenerator (finite_field_primitive_powers_all hd hg)
    (by rw [Nat.card_units, labelField_card hd])

theorem cyclicStateEquiv_integer {d : ℕ} (hd : 0 < d) (g : (LabelField d)ˣ)
    (hg : orderOf g = 2^d-1) (j : ℤ) :
    cyclicStateEquiv hd g hg (Multiplicative.ofAdd (j : ZMod (2^d-1))) = g^j := by
  exact zmodMulEquivOfGenerator_apply_ofAdd_intCast _ _ j

theorem cyclicStateEquiv_shift {d : ℕ} (hd : 0 < d) (g : (LabelField d)ˣ)
    (hg : orderOf g = 2^d-1) (j k : ZMod (2^d-1)) :
    cyclicStateEquiv hd g hg (Multiplicative.ofAdd (j+k)) =
      cyclicStateEquiv hd g hg (Multiplicative.ofAdd j) *
        cyclicStateEquiv hd g hg (Multiplicative.ofAdd k) :=
  map_mul (cyclicStateEquiv hd g hg) _ _

#print axioms finite_field_primitive_powers_all
#print axioms cyclicStateEquiv_integer
#print axioms cyclicStateEquiv_shift

end CenteredCubeSqrt
