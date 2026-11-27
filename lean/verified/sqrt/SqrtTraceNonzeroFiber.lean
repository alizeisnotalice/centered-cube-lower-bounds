import SqrtTracePairing
import Mathlib.Data.Finset.Erase

namespace CenteredCubeSqrt
open Classical

/-- Passing from the whole field to the cyclic sequence of nonzero states
subtracts exactly one and only from the all-zero output fiber. -/
theorem finite_linear_nonzero_fiber {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    [Module (ZMod 2) V] [Module (ZMod 2) W] [Finite V]
    (f : V →ₗ[ZMod 2] W) (y : W) :
    Nat.card {v : V // f v = y ∧ v ≠ 0} =
      Nat.card {v : V // f v = y} - if y = 0 then 1 else 0 := by
  classical
  let : Fintype V := Fintype.ofFinite V
  let candidates : Finset V := Finset.univ.filter (fun v => f v = y)
  have eq :
      Finset.univ.filter (fun v : V => f v = y ∧ v ≠ 0) = candidates.erase 0 := by
    ext x
    simp [candidates, and_comm]
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype,
    Fintype.card_subtype, eq]
  change (candidates.erase 0).card = candidates.card - _
  by_cases hy : y=0
  · have hz : (0:V) ∈ candidates := by simp [candidates,hy]
    rw [Finset.card_erase_of_mem hz, ite_eq_left hy]
  · have hz : (0:V) ∉ candidates := by simp [candidates, Ne.symm hy]
    rw [Finset.erase_eq_of_notMem hz, ite_eq_right hy, Nat.sub_zero]

#print axioms finite_linear_nonzero_fiber

end CenteredCubeSqrt
