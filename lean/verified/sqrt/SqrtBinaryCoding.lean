import SqrtLabelSpace
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Algebra.BigOperators.Fin

namespace CenteredCubeSqrt

open scoped BigOperators

/-- Label bits, with exactly the manuscript's little-endian integer coding. -/
def binaryLabelEquiv : (b : ℕ) → (Fin b → ZMod 2) ≃ Fin (2^b)
  | 0 =>
    { toFun := fun _ => 0
      invFun := fun _ => Fin.elim0
      left_inv := fun _ => funext (fun i => Fin.elim0 i)
      right_inv := fun x => Fin.ext (show 0 = x.val from by have h : x.val < 1 := x.isLt; omega) }
  | b+1 =>
    (Fin.snocEquiv (fun _ : Fin (b+1) => ZMod 2)).symm.trans
      ((Equiv.prodCongr (Equiv.refl (Fin 2)) (binaryLabelEquiv b)).trans
        (finProdFinEquiv.trans (finCongr (pow_succ' 2 b).symm)))

theorem binaryLabelEquiv_val (b : ℕ) (y : Fin b → ZMod 2) :
    (binaryLabelEquiv b y).val = ∑ i, 2^i.val * (y i).val := by
  induction b with
  | zero => simp [binaryLabelEquiv]
  | succ b ih =>
    rw [Fin.sum_univ_castSucc]
    change (binaryLabelEquiv b (Fin.init y)).val + 2^b*(y (Fin.last b)).val = _
    rw [ih]
    rfl

theorem binaryLabelEquiv_zero (b : ℕ) : (binaryLabelEquiv b 0).val = 0 := by
  rw [binaryLabelEquiv_val]
  apply Finset.sum_eq_zero
  intro i _
  have hz : (0 : ZMod 2).val = 0 := rfl
  exact (Nat.mul_zero _ : 2^i.val * 0 = 0)

#print axioms binaryLabelEquiv_val
#print axioms binaryLabelEquiv_zero

end CenteredCubeSqrt
