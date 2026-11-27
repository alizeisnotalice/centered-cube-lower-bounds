import SqrtRawCellEnergy

namespace CenteredCubeSqrt
open MeasureTheory Set
open scoped Interval BigOperators

theorem sum_midpoint_numerators (B : ℕ) :
    (∑ j ∈ Finset.range B,((j:ℝ)+1/2))=(B:ℝ)^2/2 := by
  induction B with
  | zero => norm_num
  | succ B ih => rw [Finset.sum_range_succ, ih,Nat.cast_succ]; ring

theorem sum_midpoint_numerator_squares (B : ℕ) :
    (∑ j ∈ Finset.range B,((j:ℝ)+1/2)^2)=((B:ℝ)^3)/3-(B:ℝ)/12 := by
  induction B with
  | zero => norm_num
  | succ B ih => rw [Finset.sum_range_succ,ih,Nat.cast_succ]; ring

theorem one_cell_average_raw_energy {B : ℕ} (hB : 0<B) :
    (1/(B:ℝ))*(∑ y : Fin B, ∫ r in (0:ℝ)..1,(cellPrimitive (labelCellMidpoint y) r)^2) =
      1/6-1/(12*(B:ℝ)^2) := by
  have hB0 : (B:ℝ)≠0 := by exact_mod_cast hB.ne'
  simp_rw [label_cell_energy]
  unfold labelCellMidpoint
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ =>
    (((j:ℝ)+1/2)/(B:ℝ))^2-((j:ℝ)+1/2)/(B:ℝ)+1/3)]
  simp_rw [div_pow]
  rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,←Finset.sum_div,←Finset.sum_div,
    sum_midpoint_numerators,sum_midpoint_numerator_squares,Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  field_simp
  ring

#print axioms one_cell_average_raw_energy

end CenteredCubeSqrt
