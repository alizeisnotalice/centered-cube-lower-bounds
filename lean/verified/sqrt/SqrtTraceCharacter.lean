import SqrtDefectHyperplane
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.NormNum

namespace CenteredCubeSqrt

open scoped BigOperators

/-- The literal character ((-1)^{mathrm{val},z}) of F₂. -/
noncomputable def bitCharacter (z : ZMod 2) : ℝ := (-1)^z.val

theorem bitCharacter_add (x y : ZMod 2) :
    bitCharacter (x+y) = bitCharacter x * bitCharacter y := by
  have h0 : (0:ZMod 2).val = 0 := rfl
  have h1 : (1:ZMod 2).val = 1 := rfl
  have h2 : (1:ZMod 2)+1=0 := rfl
  have h2n : (2:ZMod 2).val = 0 := rfl
  rcases zmod_two_zero_or_one x with rfl | rfl <;>
    rcases zmod_two_zero_or_one y with rfl | rfl <;>
    norm_num [bitCharacter,h0,h1,h2,h2n]

theorem one_add_bitCharacter (z : ZMod 2) :
    1 + bitCharacter z = if z=0 then 2 else 0 := by
  have h0 : (0:ZMod 2).val = 0 := rfl
  have h1 : (1:ZMod 2).val = 1 := rfl
  rcases zmod_two_zero_or_one z with rfl | rfl <;>
    norm_num [bitCharacter,h0,h1]

/-- This is the exact 0/2 Walsh multiplier for the unique defect match. -/
theorem defect_walsh_multiplier {b : ℕ} (a c : NonzeroBinary b) (y : LabelOutput b) :
    1 +
      bitCharacter (∑ i, if a.1 i then y (.inl i) else 0) *
      bitCharacter (∑ i, if c.1 i then y (.inr i) else 0) =
      if traceMatchForm a c y=0 then 2 else 0 := by
  rw [← bitCharacter_add, ← traceMatchForm_apply, one_add_bitCharacter]

#print axioms defect_walsh_multiplier

end CenteredCubeSqrt
