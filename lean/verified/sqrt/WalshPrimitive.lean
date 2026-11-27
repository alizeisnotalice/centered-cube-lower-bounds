import OrdinalWalsh
import SqrtRawRegularCorrelation
import Mathlib.Tactic.Ring

namespace CenteredCubeSqrt
open MeasureTheory Set Classical
open scoped BigOperators Interval
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

noncomputable def walshCellPrimitive {b : ℕ} (a : NonzeroBinary b) (r : ℝ) : ℝ :=
  (∑ y : Fin (2^b), ordinalWalsh a y * cellPrimitive (labelCellMidpoint y) r) / (2:ℝ)^b

theorem walshCellPrimitive_measurable {b : ℕ} (a : NonzeroBinary b) :
    Measurable (walshCellPrimitive a) := by
  exact (Finset.measurable_sum _ fun y _ => (cellPrimitive_measurable _).const_mul _).div_const _

theorem walshCell_moment {m : ℕ} (a c : NonzeroBinary m)
    {l r s : ℝ} (hlr : l≤r) (hl : 0≤l) (hr : r≤1) (hls : 0≤l+s) (hrs : r+s≤1) :
    (1/((2:ℝ)^m)^2) * (∑ p : Fin (2^m) × Fin (2^m),
        ordinalWalsh a p.1 * ordinalWalsh c p.2 *
        ∫ t in l..r, cellPrimitive (labelCellMidpoint p.1) t * cellPrimitive (labelCellMidpoint p.2) (t+s)) =
      ∫ t in l..r, walshCellPrimitive a t * walshCellPrimitive c (t+s) := by
  simp_rw [← intervalIntegral.integral_const_mul]
  rw [←intervalIntegral.integral_finsetSum, ← intervalIntegral.integral_const_mul]
  · apply intervalIntegral.integral_congr
    intro t _
    unfold walshCellPrimitive
    dsimp (config := { proj := false }) only
    let F (y : Fin (2^m)) := ordinalWalsh a y * cellPrimitive (labelCellMidpoint y) t
    let G (y : Fin (2^m)) := ordinalWalsh c y * cellPrimitive (labelCellMidpoint y) (t+s)
    have e : (∑ p : Fin (2^m) × Fin (2^m), ordinalWalsh a p.1 * ordinalWalsh c p.2 *
        (cellPrimitive (labelCellMidpoint p.1) t * cellPrimitive (labelCellMidpoint p.2) (t+s))) =
        (∑ y, F y)*(∑ y, G y) := by
      rw [Fintype.sum_prod_type, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      unfold F G
      ring
    rw [e]
    change 1 / ((2:ℝ)^m)^2 * ((∑ y,F y)*(∑ y,G y)) =
      ((∑ y,F y)/(2:ℝ)^m)*((∑ y,G y)/(2:ℝ)^m)
    have h : (2:ℝ)^m ≠ 0 := pow_ne_zero _ (by norm_num)
    field_simp
  · exact fun p _ => (labelCellPrimitive_prod_intervalIntegrable p hlr hl hr hls hrs).const_mul _

#print axioms walshCell_moment
end CenteredCubeSqrt
