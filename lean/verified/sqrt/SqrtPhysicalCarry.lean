import Mathlib.Data.Int.ModEq
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

namespace CenteredCubeSqrt

/-- The integer fine mesh coordinate of a point in the coarse cell `j` with label `y`.
The half-unit offset common to each point cancels in all differences. -/
def labelCoord (B j y : ℤ) : ℤ := j*B+y

/-- In the fine mesh, the only possible carries for a difference kB+b are k and k+1. -/
theorem label_carry_iff {B b k j l y z : ℤ}
    (hy : 0 ≤ y ∧ y < B) (hz : 0 ≤ z ∧ z < B) (hb : 0 ≤ b ∧ b < B) :
    labelCoord B l z - labelCoord B j y = k*B+b ↔
    (l-j = k ∧ z-y = b) ∨ (l-j = k+1 ∧ z-y = b-B) := by
  have hB : 0 < B := by omega
  constructor
  · intro h
    have e : (l-j-k)*B = b-z+y := by unfold labelCoord at h; linarith [show (l-j-k)*B = l*B-j*B-k*B by ring]
    have lower : 0 ≤ l-j-k := by
      by_contra! hn
      have hmul := mul_le_mul_of_nonneg_right (show l-j-k ≤ -1 by omega) hB.le
      nlinarith [hmul, e, hz.2, hy.1, hb.1]
    have upper : l-j-k ≤ 1 := by
      by_contra! hn
      have hmul := mul_le_mul_of_nonneg_right (show 2 ≤ l-j-k by omega) hB.le
      nlinarith [hmul, e, hy.2, hz.1, hb.2]
    rcases (show l-j-k = 0 ∨ l-j-k = 1 by omega) with h0 | h1
    · left
      rw [h0, zero_mul] at e
      omega
    · right
      rw [h1, one_mul] at e
      omega
  · intro h
    rcases h with ⟨hl, hd⟩ | ⟨hl, hd⟩
    · unfold labelCoord
      linear_combination B*hl + hd
    · unfold labelCoord
      linear_combination B*hl + hd

/-- Circular version: reducing modulo the physical period preserves the two
carry classes, with the coarse shift taken modulo the cell count. -/
theorem label_carry_mod_iff {B K b k j l y z : ℤ}
    (hy : 0 ≤ y ∧ y < B) (hz : 0 ≤ z ∧ z < B) (hb : 0 ≤ b ∧ b < B) :
    (labelCoord B l z - labelCoord B j y ≡ k*B+b [ZMOD B*K]) ↔
    ((l-j ≡ k [ZMOD K]) ∧ z-y = b) ∨
      ((l-j ≡ k+1 [ZMOD K]) ∧ z-y = b-B) := by
  constructor
  · intro h
    obtain ⟨t,ht⟩ := Int.modEq_iff_add_fac.mp h.symm
    have he : labelCoord B (l-K*t) z - labelCoord B j y = k*B+b := by
      unfold labelCoord at ht ⊢
      linear_combination ht
    rcases (label_carry_iff hy hz hb).mp he with ⟨hs,hz'⟩ | ⟨hs,hz'⟩
    · left
      refine ⟨Int.modEq_iff_add_fac.mpr ⟨-t, ?_⟩, hz'⟩
      linarith
    · right
      refine ⟨Int.modEq_iff_add_fac.mpr ⟨-t, ?_⟩, hz'⟩
      linarith
  · intro h
    apply Int.ModEq.symm
    apply Int.modEq_iff_add_fac.mpr
    rcases h with ⟨hs,hz'⟩ | ⟨hs,hz'⟩
    · obtain ⟨t,ht⟩ := Int.modEq_iff_add_fac.mp hs.symm
      refine ⟨t,?_⟩
      unfold labelCoord
      linear_combination B*ht + hz'
    · obtain ⟨t,ht⟩ := Int.modEq_iff_add_fac.mp hs.symm
      refine ⟨t,?_⟩
      unfold labelCoord
      linear_combination B*ht + hz'

/-- The real half-offset in the manuscript agrees with the integer mesh difference. -/
theorem physical_atom_diff {K B : ℝ} (hK : K ≠ 0) (hB : B ≠ 0) (j l y z : ℝ) :
    (l+(z+1/2)/B)/K - (j+(y+1/2)/B)/K = ((l-j)*B+(z-y))/(K*B) := by
  field_simp
  ring

#print axioms label_carry_iff
#print axioms label_carry_mod_iff
#print axioms physical_atom_diff

end CenteredCubeSqrt
