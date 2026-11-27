import SqrtCyclicStates
import SqrtJointTrace

namespace CenteredCubeSqrt

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

noncomputable def phaseState {d : ℕ} (hd : 0 < d) (g : (LabelField d)ˣ)
    (hg : orderOf g = 2^d-1) (j : ZMod (2^d-1)) : (LabelField d)ˣ :=
  cyclicStateEquiv hd g hg (Multiplicative.ofAdd j)

noncomputable def phaseLabel {b d : ℕ} (hd : 0 < d) (g : (LabelField d)ˣ)
    (hg : orderOf g = 2^d-1) (t : Fin b → LabelField d) (j : ZMod (2^d-1)) :
    Fin b → ZMod 2 :=
  traceLabelMap t (phaseState hd g hg j : LabelField d)

theorem phaseLabel_joint {b d : ℕ} (hd : 0 < d) (g : (LabelField d)ˣ)
    (hg : orderOf g = 2^d-1) (t : Fin b → LabelField d)
    (j k : ZMod (2^d-1)) :
    jointTrace t (phaseState hd g hg k) (phaseState hd g hg j) =
      Sum.elim (phaseLabel hd g hg t j) (phaseLabel hd g hg t (j+k)) := by
  funext i
  rcases i with i | i
  · rfl
  · change Algebra.trace (ZMod 2) (LabelField d)
      (((phaseState hd g hg k : LabelField d)*t i)*(phaseState hd g hg j : LabelField d)) =
      Algebra.trace (ZMod 2) (LabelField d) (t i*(phaseState hd g hg (j+k) : LabelField d))
    rw [show phaseState hd g hg (j+k) = phaseState hd g hg j * phaseState hd g hg k from
      cyclicStateEquiv_shift hd g hg j k, Units.val_mul]
    congr 1
    ac_rfl

/-- A full phase scan counts precisely the nonzero field states in the
trace-label fiber, with no extra uniformity or randomness assumption. -/
theorem phaseLabel_fiber_count {b d : ℕ} (hd : 0 < d) (g : (LabelField d)ˣ)
    (hg : orderOf g = 2^d-1) (t : Fin b → LabelField d)
    (k : ZMod (2^d-1)) (y : LabelOutput b) :
    Nat.card {j : ZMod (2^d-1) //
      Sum.elim (phaseLabel hd g hg t j) (phaseLabel hd g hg t (j+k)) = y} =
      Nat.card {x : LabelField d // jointTrace t (phaseState hd g hg k) x = y ∧ x ≠ 0} := by
  apply Nat.card_congr
  let E := cyclicStateEquiv hd g hg
  refine {
    toFun := fun j => ⟨phaseState hd g hg j.1,
      (phaseLabel_joint hd g hg t j.1 k).trans j.2, Units.ne_zero _⟩
    invFun := fun x => ⟨(E.symm (Units.mk0 x.1 x.2.2)).toAdd, ?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · rw [← phaseLabel_joint]
    change jointTrace t (phaseState hd g hg k)
      (E (E.symm (Units.mk0 x.1 x.2.2)) : LabelField d) = y
    rw [MulEquiv.apply_symm_apply]
    exact x.2.1
  · intro j
    apply Subtype.ext
    change (E.symm (Units.mk0 (E (Multiplicative.ofAdd j.1) : LabelField d) _)).toAdd = j.1
    have he : Units.mk0 (E (.ofAdd j.1) : LabelField d) (Units.ne_zero _) = E (.ofAdd j.1) :=
      Units.ext rfl
    rw [he, MulEquiv.symm_apply_apply]
    rfl
  · intro x
    apply Subtype.ext
    change (E (E.symm (Units.mk0 x.1 x.2.2)) : LabelField d) = x.1
    rw [MulEquiv.apply_symm_apply]
    rfl

#print axioms phaseLabel_joint
#print axioms phaseLabel_fiber_count

end CenteredCubeSqrt
