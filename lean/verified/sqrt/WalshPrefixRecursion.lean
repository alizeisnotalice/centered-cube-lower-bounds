import WalshBitSplit
import Mathlib.Algebra.BigOperators.Intervals

namespace CenteredCubeSqrt
open scoped BigOperators
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

noncomputable def walshNat {b : ℕ} (a : Fin b → Bool) (y : ℕ) : ℝ :=
  binaryWalsh a ((binaryLabelEquiv b).symm ⟨y % 2^b, Nat.mod_lt _ (Nat.two_pow_pos _)⟩)

noncomputable def walshPrefix {b : ℕ} (a : Fin b → Bool) (j : ℕ) : ℝ :=
  ∑ y ∈ Finset.range j, walshNat a y

theorem walshNat_succ_half {b : ℕ} (a : Fin (b+1) → Bool)
    (y h : ℕ) (hy : y < 2^b) (hh : h < 2) :
    walshNat a (y + 2^b*h) =
    walshNat (Fin.init a) y * bitCharacter (if a (Fin.last b) then (h : ZMod 2) else 0) := by
  let low := (binaryLabelEquiv b).symm (⟨y, hy⟩ : Fin (2^b))
  have hl : (binaryLabelEquiv b low).val = y := by simp [low]
  have hd : ((h:ZMod 2)).val = h := by rw [ZMod.val_natCast, Nat.mod_eq_of_lt hh]
  have h2 : y + 2^b*h < 2^(b+1) := by
    rw [pow_succ]
    interval_cases h <;> omega
  have e : (binaryLabelEquiv (b+1)) (Fin.snoc low (h : ZMod 2)) =
      ⟨(y+2^b*h) % 2^(b+1),Nat.mod_lt _ (Nat.two_pow_pos _)⟩ := by
    apply Fin.ext
    simp only [Nat.mod_eq_of_lt h2]
    rw [binaryOrdinal_snoc, hl, hd]
  unfold walshNat
  rw [← e, Equiv.symm_apply_apply, binaryWalsh_snoc]
  simp only [low, Nat.mod_eq_of_lt hy]

theorem walshPrefix_succ_first_half {b : ℕ} (a : Fin (b+1) → Bool)
    (j : ℕ) (hj : j ≤ 2^b) :
    walshPrefix a j = walshPrefix (Fin.init a) j := by
  unfold walshPrefix
  apply Finset.sum_congr rfl
  intro y hy
  have hy' : y < 2^b := (Finset.mem_range.mp hy).trans_le hj
  have e := walshNat_succ_half a y 0 hy' (by decide)
  simpa [bitCharacter] using e

theorem walshPrefix_succ_second_half {b : ℕ} (a : Fin (b+1) → Bool)
    (j : ℕ) (hj : j ≤ 2^b) :
    walshPrefix a (2^b+j) = walshPrefix (Fin.init a) (2^b) +
       bitCharacter (if a (Fin.last b) then 1 else 0) * walshPrefix (Fin.init a) j := by
  unfold walshPrefix
  rw [Finset.sum_range_add, Finset.mul_sum]
  change (walshPrefix a (2^b)) + _ = (walshPrefix (Fin.init a) (2^b)) + _
  rw [walshPrefix_succ_first_half a _ le_rfl]
  congr 1
  apply Finset.sum_congr rfl
  intro y hy
  have hy' : y < 2^b := (Finset.mem_range.mp hy).trans_le hj
  have e := walshNat_succ_half a y 1 hy' (by decide)
  simpa [add_comm, mul_comm] using e

#print axioms walshNat_succ_half
#print axioms walshPrefix_succ_second_half
end CenteredCubeSqrt
