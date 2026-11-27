import SqrtPaperLabelCount
import SqrtTraceCharacter
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

open scoped BigOperators

namespace CenteredCubeSqrt

open Classical
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- The paper's defective count in its literal real-valued Walsh form. -/
theorem manuscript_defective_walsh_count {b d : ℕ} (hd : 0 < d)
    (hb : 0 < b) (hdim : 2*b ≤ d)
    (g : (LabelField d)ˣ) (hg : orderOf g = 2^d-1) {t : Fin b → LabelField d}
    (ht : LinearIndependent (ZMod 2) t) (k : ZMod (2^d-1))
    (hk : (phaseState hd g hg k : LabelField d) ≠ 1)
    (hk' : (phaseState hd g hg k : LabelField d) ∈ labelRatioSet t)
    (hS : MultiplicativeSidon {x : LabelField d | x ∈ labelSpace t ∧ x ≠ 0})
    (a c : NonzeroBinary b)
    (hmatch : labelValue t a = (phaseState hd g hg k : LabelField d)*labelValue t c)
    (y : LabelOutput b) :
    (Nat.card {j : ZMod (2^d-1) //
      Sum.elim (phaseLabel hd g hg t j) (phaseLabel hd g hg t (j+k)) = y} : ℝ) =
      (2:ℝ)^d/((2:ℝ)^b)^2 *
        (1 + bitCharacter (∑ i, if a.1 i then y (.inl i) else 0) *
          bitCharacter (∑ i, if c.1 i then y (.inr i) else 0)) - (if y=0 then 1 else 0) := by
  rw [defect_walsh_multiplier, manuscript_defective_cyclic_label_count hd g hg ht k hk hk' hS a c hmatch]
  have hab : d-(2*b-1) = d-2*b+1 := by omega
  have hpow : (2:ℝ)^(d-(2*b-1)) = (2:ℝ)^d/((2:ℝ)^b)^2 * 2 := by
    have hbase : (2:ℝ)^(d-2*b)*((2:ℝ)^b)^2 = (2:ℝ)^d := by
      rw [← pow_mul, Nat.mul_comm b 2, ← pow_add, Nat.sub_add_cancel hdim]
    rw [hab, pow_succ, ← hbase]
    field_simp
  by_cases hy : traceMatchForm a c y=0
  · rw [ite_eq_left hy, ite_eq_left hy]
    by_cases hy0 : y=0
    · rw [ite_eq_left hy0, ite_eq_left hy0, Nat.cast_sub (show 1 ≤ (2:ℕ)^(d-(2*b-1)) from Nat.one_le_two_pow)]
      simpa only [Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat] using congrArg (fun z : ℝ => z-1) hpow
    · rw [ite_eq_right hy0, ite_eq_right hy0, Nat.sub_zero, sub_zero]
      simpa only [Nat.cast_pow, Nat.cast_ofNat] using hpow
  · have hy0 : y≠0 := fun e => hy (e ▸ map_zero (traceMatchForm a c))
    rw [ite_eq_right hy, ite_eq_right hy, ite_eq_right hy0, mul_zero, sub_zero, Nat.cast_zero]

#print axioms manuscript_defective_walsh_count

end CenteredCubeSqrt
