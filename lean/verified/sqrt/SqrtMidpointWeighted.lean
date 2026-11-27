import SqrtNearQuantizer
import SqrtTriangularFubini
namespace CenteredCubeSqrt
open MeasureTheory Set
open scoped Interval BigOperators
set_option maxHeartbeats 1000000

theorem midpointError_all_intervalIntegrable {B : ℕ} (hB : 0<B) (a b : ℝ) :
    IntervalIntegrable (midpointError B) volume a b := by
  have hB' : 0<(B:ℝ) := by exact_mod_cast hB
  rw [intervalIntegrable_iff]
  apply Measure.integrableOn_of_bounded (M:=1+|a|+|b|) (s_finite:=by rw [uIoc]; simp [Real.volume_Ioc])
    (midpointError_measurable hB).aestronglyMeasurable
  filter_upwards [ae_restrict_mem (μ:=volume) measurableSet_uIoc] with x hx
  rw [Real.norm_eq_abs]
  have e : |x|≤|a|+|b| := by
    have H := uIoc_subset_uIcc hx
    rw [abs_le]
    constructor
    · have a' := (abs_le.mp (le_refl |a|)).1
      have b' := (abs_le.mp (le_refl |b|)).1
      have H : min a b≤x := H.1
      rcases le_total a b with h|h
      · rw [min_eq_left h] at H
        linarith [abs_nonneg b]
      · rw [min_eq_right h] at H
        linarith [abs_nonneg a]
    · have a' := le_abs_self a
      have b' := le_abs_self b
      have hh : x≤max a b := H.2
      rcases le_total a b with h|h
      · rw [max_eq_right h] at hh
        linarith [abs_nonneg a]
      · rw [max_eq_left h] at hh
        linarith [abs_nonneg b]
  let C := (((Finset.range B).filter (fun z : ℕ => ((z:ℝ)+1/2)/(B:ℝ)≤x)).card:ℝ)/(B:ℝ)
  have hC : 0≤C ∧ C≤1 := by
    have hc := Finset.card_filter_le (s:=Finset.range B)
      (p:=fun z : ℕ => ((z:ℝ)+1/2)/(B:ℝ)≤x)
    rw [Finset.card_range] at hc
    exact ⟨by dsimp [C]; positivity,(div_le_one hB').mpr (by exact_mod_cast hc)⟩
  change |C-x|≤_
  have t := abs_add_le C (-x)
  rw [←sub_eq_add_neg,abs_neg,abs_of_nonneg hC.1] at t
  exact t.trans (by linarith [hC.2])

theorem actualMidpointPrefix_continuous {B : ℕ} (hB : 0<B) :
    Continuous (actualMidpointPrefix B) := intervalIntegral.continuous_primitive
      (midpointError_all_intervalIntegrable hB) 0

theorem weighted_midpoint_left_exact {B : ℕ} (hB : 0<B) {a : ℝ} (ha : a∈Icc (0:ℝ) 1) :
    (∫ r in (0:ℝ)..a,(a-r)*midpointError B r) =
      ∫ r in (0:ℝ)..a,actualMidpointPrefix B r := by
  symm
  exact triangular_prefix_Fubini (midpointError_measurable hB) ha.1
    (fun r hr => midpointError_abs_le_half_cell hB ⟨hr.1,hr.2.trans ha.2⟩)

theorem weighted_midpoint_right_exact {B : ℕ} (hB : 0<B) {θ : ℝ} (hθ : θ∈Icc (0:ℝ) 1) :
    -(∫ r in (0:ℝ)..(1-θ),r*midpointError B (r+θ)) =
      ∫ r in (0:ℝ)..(1-θ),actualMidpointPrefix B (r+θ) := by
  let P := actualMidpointPrefix B
  let e := midpointError B
  have adj (y : ℝ) : (∫ x in θ..y,e x)=P y-P θ := by
    have hh := intervalIntegral.integral_add_adjacent_intervals
      (midpointError_all_intervalIntegrable hB 0 θ) (midpointError_all_intervalIntegrable hB θ y)
    unfold P actualMidpointPrefix
    linarith
  have h0 : P 1=0 := by
    have h := midpointError_grid_prefix_zero (B:=B) (j:=B) le_rfl
    have hb : (B:ℝ)≠0 := by exact_mod_cast hB.ne'
    rwa [div_self hb] at h
  have intC : IntervalIntegrable (fun _ : ℝ => P θ) volume θ 1 := intervalIntegrable_const
  have intP : IntervalIntegrable P volume θ 1 := (actualMidpointPrefix_continuous hB).intervalIntegrable _ _
  have hh := triangular_prefix_Fubini (midpointError_measurable hB) hθ.2
    (fun r hr => midpointError_abs_le_half_cell hB ⟨hθ.1.trans hr.1,hr.2⟩)
  change (∫ y in θ..1, ∫ x in θ..y,e x)=(∫ y in θ..1,(1-y)*e y) at hh
  simp_rw [adj] at hh
  rw [intervalIntegral.integral_sub intP intC,intervalIntegral.integral_const,smul_eq_mul] at hh
  have e₁ (r : ℝ) : r*e (r+θ)=((r+θ)-θ)*e (r+θ) := by rw [add_sub_cancel_right]
  change -(∫ r in (0:ℝ)..(1-θ),r*e (r+θ)) =
      ∫ r in (0:ℝ)..(1-θ),P (r+θ)
  simp_rw [e₁]
  rw [intervalIntegral.integral_comp_add_right (f:=fun y => (y-θ)*e y) (a:=0) (b:=1-θ) θ,
    intervalIntegral.integral_comp_add_right (f:=P) (a:=0) (b:=1-θ) θ,zero_add,sub_add_cancel]
  have e₂ (y : ℝ) : (y-θ)*e y=(1-θ)*e y-(1-y)*e y := by ring
  simp_rw [e₂]
  have ie := midpointError_all_intervalIntegrable hB θ 1
  have c : ContinuousOn (fun y : ℝ => 1-y) [[θ,1]] := (continuous_const.sub continuous_id).continuousOn
  rw [intervalIntegral.integral_sub (ie.const_mul _) (ie.continuousOn_mul c),
    intervalIntegral.integral_const_mul,adj,h0,zero_sub]
  linarith

#print axioms weighted_midpoint_left_exact
#print axioms weighted_midpoint_right_exact
end CenteredCubeSqrt
