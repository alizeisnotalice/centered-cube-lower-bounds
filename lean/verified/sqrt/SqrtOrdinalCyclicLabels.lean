import SqrtBinaryCoding
import SqrtPaperLabelCount

namespace CenteredCubeSqrt

open Classical
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- The exact integer label y_j used in the atom coordinates. -/
noncomputable def ordinalPhaseLabel {b d : ℕ} (hd : 0 < d) (g : (LabelField d)ˣ)
    (hg : orderOf g = 2^d-1) (t : Fin b → LabelField d) (j : ZMod (2^d-1)) : Fin (2^b) :=
  binaryLabelEquiv b (phaseLabel hd g hg t j)

/-- The original regular label-law statement with integer labels y,z as
opposed to digit vectors. -/
theorem regular_ordinal_cyclic_label_count {b d : ℕ} (hd : 0 < d)
    (g : (LabelField d)ˣ) (hg : orderOf g = 2^d-1) {t : Fin b → LabelField d}
    (ht : LinearIndependent (ZMod 2) t) (k : ZMod (2^d-1))
    (hk : (phaseState hd g hg k : LabelField d) ≠ 1)
    (hk' : (phaseState hd g hg k : LabelField d) ∉ labelRatioSet t)
    (hdim : 2*b ≤ d) (y z : Fin (2^b)) :
    Nat.card {j : ZMod (2^d-1) //
      ordinalPhaseLabel hd g hg t j = y ∧ ordinalPhaseLabel hd g hg t (j+k) = z} =
      2^d/(2^b)^2 - if y.val=0 ∧ z.val=0 then 1 else 0 := by
  let u := (binaryLabelEquiv b).symm y
  let v := (binaryLabelEquiv b).symm z
  let target : LabelOutput b := Sum.elim u v
  have e0 : target = 0 ↔ y.val=0 ∧ z.val=0 := by
    constructor
    · intro h
      have hu : u=0 := by funext i; exact congrFun h (.inl i)
      have hv : v=0 := by funext i; exact congrFun h (.inr i)
      constructor
      · rw [← (binaryLabelEquiv b).apply_symm_apply y, show (binaryLabelEquiv b).symm y = 0 from hu]
        exact binaryLabelEquiv_zero b
      · rw [← (binaryLabelEquiv b).apply_symm_apply z, show (binaryLabelEquiv b).symm z = 0 from hv]
        exact binaryLabelEquiv_zero b
    · rintro ⟨hy,hz⟩
      have eu : (binaryLabelEquiv b) u = (binaryLabelEquiv b) 0 := by
        apply Fin.ext
        change ((binaryLabelEquiv b) ((binaryLabelEquiv b).symm y)).val = _
        rw [(binaryLabelEquiv b).apply_symm_apply y,binaryLabelEquiv_zero,hy]
      have ev : (binaryLabelEquiv b) v = (binaryLabelEquiv b) 0 := by
        apply Fin.ext
        change ((binaryLabelEquiv b) ((binaryLabelEquiv b).symm z)).val = _
        rw [(binaryLabelEquiv b).apply_symm_apply z,binaryLabelEquiv_zero,hz]
      have hu := (binaryLabelEquiv b).injective eu
      have hv := (binaryLabelEquiv b).injective ev
      funext i
      cases i with
      | inl i => exact congrFun hu i
      | inr i => exact congrFun hv i
  have eq : Nat.card {j : ZMod (2^d-1) //
      ordinalPhaseLabel hd g hg t j = y ∧ ordinalPhaseLabel hd g hg t (j+k) = z} =
      Nat.card {j : ZMod (2^d-1) //
      Sum.elim (phaseLabel hd g hg t j) (phaseLabel hd g hg t (j+k)) = target} := by
    apply Nat.card_congr (Equiv.subtypeEquiv (Equiv.refl _) ?_)
    intro j
    constructor
    · rintro ⟨h1,h2⟩
      have h1' : phaseLabel hd g hg t j = u := by
        apply (binaryLabelEquiv b).injective
        rwa [show (binaryLabelEquiv b) u = y from (binaryLabelEquiv b).apply_symm_apply y]
      have h2' : phaseLabel hd g hg t (j+k) = v := by
        apply (binaryLabelEquiv b).injective
        rwa [show (binaryLabelEquiv b) v = z from (binaryLabelEquiv b).apply_symm_apply z]
      change Sum.elim (phaseLabel hd g hg t j) (phaseLabel hd g hg t (j+k)) = target
      rw [h1',h2']
    · intro h
      have h1' : phaseLabel hd g hg t j = u := by funext i; exact congrFun h (.inl i)
      have h2' : phaseLabel hd g hg t (j+k) = v := by funext i; exact congrFun h (.inr i)
      unfold ordinalPhaseLabel
      rw [h1', h2']
      exact ⟨(binaryLabelEquiv b).apply_symm_apply y,(binaryLabelEquiv b).apply_symm_apply z⟩
  rw [eq, manuscript_regular_cyclic_label_count hd g hg ht k hk hk' hdim]
  simp [e0]

#print axioms regular_ordinal_cyclic_label_count

end CenteredCubeSqrt
