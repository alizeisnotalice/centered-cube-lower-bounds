import WalshPrefixRecursion
import SqrtWalshEnergyArithmetic

namespace CenteredCubeSqrt
open scoped BigOperators
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem walshScalar_sq (a : Bool) : (bitCharacter (if a then 1 else 0))^2 = 1 := by
  cases a <;> norm_num [bitCharacter, show (0:ZMod 2).val=0 from rfl, show (1:ZMod 2).val=1 from rfl]

theorem walshPrefix_zero {b : ℕ} (j : ℕ) :
    walshPrefix (fun _ : Fin b => false) j = j := by
  simp [walshPrefix, walshNat, binaryWalsh, bitCharacter, show (0:ZMod 2).val=0 from rfl]

theorem walsh_init_last_determine {b : ℕ} {a : Fin (b+1) → Bool}
    (h : Fin.init a = fun _ => false) (h' : a (Fin.last b) = false) :
    a = fun _ => false := by
  funext i
  refine Fin.lastCases h' (fun j => ?_) i
  exact congrFun h j

theorem walshPrefix_end_zero_of_nonzero {b : ℕ} (a : Fin b → Bool)
    (h : a ≠ fun _ => false) : walshPrefix a (2^b) = 0 := by
  induction b with
  | zero =>
    exfalso
    apply h
    funext i
    exact Fin.elim0 i
  | succ b ih =>
    rw [show (2:ℕ)^(b+1)=2^b+2^b by rw [pow_succ]; omega,
      walshPrefix_succ_second_half a _ le_rfl]
    by_cases hL : Fin.init a = fun _ => false
    · have ha : a (Fin.last b) = true := by
        cases e : a (Fin.last b)
        · exact (h (walsh_init_last_determine hL e)).elim
        · rfl
      rw [ha, hL, walshPrefix_zero]
      norm_num [bitCharacter, show (1:ZMod 2).val=1 from rfl]
    · rw [ih (Fin.init a) hL]
      ring

noncomputable def walshDiscreteEnergy {b : ℕ} (a : Fin b → Bool) :=
  ∑ j ∈ Finset.range (2^b), (walshPrefix a j)^2

theorem walshDiscreteEnergy_repeat {b : ℕ} (a : Fin (b+1) → Bool)
    (h : Fin.init a ≠ fun _ => false) :
    walshDiscreteEnergy a = 2 * walshDiscreteEnergy (Fin.init a) := by
  unfold walshDiscreteEnergy
  rw [show (2:ℕ)^(b+1)=2^b+2^b by rw [pow_succ]; omega, Finset.sum_range_add]
  have h₁ : (∑ j ∈ Finset.range (2^b), (walshPrefix a j)^2) =
      ∑ j ∈ Finset.range (2^b), (walshPrefix (Fin.init a) j)^2 := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [walshPrefix_succ_first_half a j (Finset.mem_range.mp hj).le]
  have h₂ : (∑ j ∈ Finset.range (2^b), (walshPrefix a (2^b+j))^2) =
      ∑ j ∈ Finset.range (2^b), (walshPrefix (Fin.init a) j)^2 := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [walshPrefix_succ_second_half a j (Finset.mem_range.mp hj).le,
      walshPrefix_end_zero_of_nonzero _ h, zero_add, mul_pow, walshScalar_sq, one_mul]
  rw [h₁,h₂,two_mul]

#print axioms walshPrefix_end_zero_of_nonzero
#print axioms walshDiscreteEnergy_repeat
end CenteredCubeSqrt
