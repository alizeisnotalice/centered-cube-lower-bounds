import SqrtRawWindowCovariance
namespace CenteredCubeSqrt
open MeasureTheory Set
open scoped Interval BigOperators
set_option maxHeartbeats 900000

theorem labelCellMidpoint_sharp {B : ℕ} (y : Fin B) :
    1/(2*(B:ℝ)) ≤ labelCellMidpoint y ∧
      labelCellMidpoint y≤1-1/(2*(B:ℝ)) := by
  have hb : 0<(B:ℝ) := by exact_mod_cast (show 0<B by have := y.isLt; omega)
  have hy : (y.val:ℝ)+1≤B := by exact_mod_cast Nat.succ_le_of_lt y.isLt
  have hy0 : 0≤(y.val:ℝ) := by positivity
  unfold labelCellMidpoint
  constructor
  · rw [show (1:ℝ)/(2*(B:ℝ))=(1/2)/(B:ℝ) by ring]
    exact div_le_div_of_nonneg_right (by linarith) hb.le
  · rw [show 1-1/(2*(B:ℝ))=((B:ℝ)-1/2)/(B:ℝ) by field_simp]
    exact div_le_div_of_nonneg_right (by linarith) hb.le

theorem actualRawPrimitive_extended_cell {B K : ℕ} [NeZero K] (f : ZMod K → Fin B)
    (j : ℤ) (r : ℝ)
    (hB : 0<B) (hr1 : -(1/(2*(B:ℝ)))<r) (hr2 : r<1+1/(2*(B:ℝ))) :
    actualRawPrimitive f (((j:ℝ)+r)/(K:ℝ)) =
      cellPrimitive (labelCellMidpoint (f (j:ZMod K))) r := by
  have hb : 0<(B:ℝ) := by exact_mod_cast hB
  have hw : 1/(2*(B:ℝ))≤1/2 := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [show (1:ℝ)≤B from by exact_mod_cast Nat.succ_le_of_lt hB]
  have hw0 : 0 < 1/(2*(B:ℝ)) := by positivity
  by_cases hr0 : 0≤r
  · by_cases h1 : r<1
    · exact actualRawPrimitive_in_cell f j ⟨hr0,h1⟩
    · have h1' : 1≤r := le_of_not_gt h1
      have hh : r-1∈Ico (0:ℝ) 1 := ⟨by linarith,by linarith⟩
      have he : ((j:ℝ)+r)/(K:ℝ)=((((j+1:ℤ):ℝ))+(r-1))/(K:ℝ) := by push_cast; ring
      rw [he,actualRawPrimitive_in_cell f (j+1) hh]
      unfold cellPrimitive
      rw [ite_eq_right (by linarith [(labelCellMidpoint_sharp (f ((j+1:ℤ):ZMod K))).1]),
        ite_eq_left (by linarith [(labelCellMidpoint_sharp (f (j:ZMod K))).2])]
      ring
  · have h0 : r<0 := lt_of_not_ge hr0
    have hh : r+1∈Ico (0:ℝ) 1 := ⟨by linarith,by linarith⟩
    have he : ((j:ℝ)+r)/(K:ℝ)=((((j-1:ℤ):ℝ))+(r+1))/(K:ℝ) := by push_cast; ring
    rw [he,actualRawPrimitive_in_cell f (j-1) hh]
    unfold cellPrimitive
    rw [ite_eq_left (by linarith [(labelCellMidpoint_sharp (f ((j-1:ℤ):ZMod K))).2]),
      ite_eq_right (by linarith [(labelCellMidpoint_sharp (f (j:ZMod K))).1])]
    ring

#print axioms actualRawPrimitive_extended_cell
end CenteredCubeSqrt
