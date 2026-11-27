import WalshPrimitive

namespace CenteredCubeSqrt
open scoped BigOperators
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

noncomputable def binaryWalsh {b : ℕ} (a : Fin b → Bool) (y : Fin b → ZMod 2) : ℝ :=
  bitCharacter (∑ i, if a i then y i else 0)

theorem binaryWalsh_snoc {b : ℕ} (a : Fin (b+1) → Bool)
    (y : Fin b → ZMod 2) (digit : ZMod 2) :
    binaryWalsh a (Fin.snoc y digit) =
    binaryWalsh (Fin.init a) y * bitCharacter (if a (Fin.last b) then digit else 0) := by
  unfold binaryWalsh
  rw [Fin.sum_univ_castSucc, bitCharacter_add]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.init]
  congr 2

theorem binaryOrdinal_snoc {b : ℕ} (y : Fin b → ZMod 2) (digit : ZMod 2) :
    (binaryLabelEquiv (b+1) (Fin.snoc y digit)).val =
    (binaryLabelEquiv b y).val + (2:ℕ)^b*digit.val := by
  rw [binaryLabelEquiv_val, Fin.sum_univ_castSucc, binaryLabelEquiv_val]
  simp

theorem binaryWalsh_eq_ordinal {b : ℕ} (a : NonzeroBinary b) (y : Fin b → ZMod 2) :
    ordinalWalsh a (binaryLabelEquiv b y) = binaryWalsh a.val y := by
  unfold ordinalWalsh binaryWalsh
  rw [Equiv.symm_apply_apply]

#print axioms binaryWalsh_snoc
#print axioms binaryOrdinal_snoc
end CenteredCubeSqrt
