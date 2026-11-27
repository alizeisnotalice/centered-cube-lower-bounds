import SqrtRawRegularPair
import SqrtRawCorrelation

namespace CenteredCubeSqrt
open MeasureTheory Set
open scoped Interval BigOperators
set_option maxHeartbeats 1600000

theorem cellPrimitive_label_mean {B : ℕ} (hB : 0<B) (r : ℝ) :
    (∑ y : Fin B, cellPrimitive (labelCellMidpoint y) r)/(B:ℝ) = midpointError B r := by
  have hB0 : (B:ℝ)≠0 := by exact_mod_cast hB.ne'
  unfold cellPrimitive labelCellMidpoint midpointError
  rw [Finset.sum_sub_distrib]
  rw [show (∑ y : Fin B,(if ((y.val:ℝ)+1/2)/(B:ℝ)≤r then (1:ℝ) else 0)) =
      ∑ y ∈ Finset.range B, (if ((y:ℝ)+1/2)/(B:ℝ)≤r then (1:ℝ) else 0) from
    Fin.sum_univ_eq_sum_range (fun y : ℕ => if ((y:ℝ)+1/2)/(B:ℝ)≤r then (1:ℝ) else 0) B]
  rw [Finset.sum_boole,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  rw [sub_div,mul_div_cancel_left₀ r hB0]

theorem labelCellPrimitive_prod_measurable {B : ℕ} (p : Fin B × Fin B) (s : ℝ) :
    Measurable (fun r : ℝ =>
      cellPrimitive (labelCellMidpoint p.1) r*cellPrimitive (labelCellMidpoint p.2) (r+s)) := by
  have hf (u : ℝ) : Measurable (cellPrimitive u) := by
    have hs : MeasurableSet {r : ℝ | u≤r} := measurableSet_Ici
    unfold cellPrimitive
    exact (Measurable.ite hs measurable_const measurable_const).sub measurable_id
  exact (hf _).mul ((hf _).comp (measurable_id.add measurable_const))

theorem labelCellPrimitive_prod_intervalIntegrable {B : ℕ} (p : Fin B × Fin B)
    {a b s : ℝ} (hab : a≤b) (h1 : 0≤a) (h2 : b≤1) (h3 : 0≤a+s) (h4 : b+s≤1) :
    IntervalIntegrable (fun r : ℝ =>
      cellPrimitive (labelCellMidpoint p.1) r*cellPrimitive (labelCellMidpoint p.2) (r+s)) volume a b := by
  rw [intervalIntegrable_iff, uIoc_of_le hab]
  apply Measure.integrableOn_of_bounded (M:=1) (s_finite:=by simp [Real.volume_Ioc])
    (labelCellPrimitive_prod_measurable p s).aestronglyMeasurable
  filter_upwards [ae_restrict_mem (μ:=volume) measurableSet_Ioc] with r hr
  rw [Real.norm_eq_abs,abs_mul]
  have hR : r∈Icc (0:ℝ) 1 := ⟨by linarith [hr.1],by linarith [hr.2]⟩
  have hS : r+s∈Icc (0:ℝ) 1 := ⟨by linarith [hr.1],by linarith [hr.2]⟩
  exact (mul_le_of_le_one_right (abs_nonneg _) (cellPrimitive_abs_le_one hS)).trans (cellPrimitive_abs_le_one hR)

theorem rawCellUniformPair_moment {B : ℕ} (hB : 0<B)
    {a b s : ℝ} (hab : a≤b) (h1 : 0≤a) (h2 : b≤1) (h3 : 0≤a+s) (h4 : b+s≤1) :
    (1/(B:ℝ)^2)*(∑ p : Fin B × Fin B,
      ∫ r in a..b,cellPrimitive (labelCellMidpoint p.1) r*cellPrimitive (labelCellMidpoint p.2) (r+s)) =
    ∫ r in a..b, midpointError B r*midpointError B (r+s) := by
  have hB0 : (B:ℝ)≠0 := by exact_mod_cast hB.ne'
  rw [←intervalIntegral.integral_finsetSum,←intervalIntegral.integral_const_mul]
  · apply intervalIntegral.integral_congr
    intro r _
    dsimp only
    rw [Fintype.sum_prod_type]
    simp_rw [←Finset.mul_sum]
    rw [←Finset.sum_mul,←cellPrimitive_label_mean hB,←cellPrimitive_label_mean hB]
    field_simp
  · exact fun p _ => labelCellPrimitive_prod_intervalIntegrable p hab h1 h2 h3 h4

#print axioms cellPrimitive_label_mean
#print axioms rawCellUniformPair_moment
end CenteredCubeSqrt
