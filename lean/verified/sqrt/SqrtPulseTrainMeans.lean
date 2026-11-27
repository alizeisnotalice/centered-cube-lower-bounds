import SqrtPulseTrain

namespace CenteredCubeSqrt

open MeasureTheory Set
open scoped BigOperators Interval

theorem smoothedWindowPulse_reflect (eps s t x : ℝ) :
    smoothedWindowPulse eps (-t) (-s) x = smoothedWindowPulse eps s t (-x) := by
  rw [smoothedWindowPulse_eq_overlap,smoothedWindowPulse_eq_overlap]
  have e1 : min (-s) (x+eps/2) = -max s (-x-eps/2) := by
    rw [← min_neg_neg]
    congr 1
    ring
  have e2 : max (-t) (x-eps/2) = -min t (-x+eps/2) := by
    rw [← max_neg_neg]
    congr 1
    ring
  rw [e1,e2,neg_sub_neg]

theorem pulseOverlap_reflect_zero (eps s t s' t' : ℝ) :
    pulseOverlap eps (-t) (-s) (-t') (-s') 0 = pulseOverlap eps s t s' t' 0 := by
  unfold pulseOverlap
  simp_rw [sub_zero, smoothedWindowPulse_reflect]
  have h := Measure.integral_comp_mul_left
    (fun x => smoothedWindowPulse eps s t x*smoothedWindowPulse eps s' t' x) (-1)
  simpa using h

theorem periodicWindowPulse_mean {eps s t C M a : ℝ}
    (he : 0 < eps) (hC : 0 < C) (hm : M/C < 1/4)
    (hs : -M ≤ s-eps/2) (ht : t+eps/2 ≤ M) (hst : s ≤ t) :
    (∫ x in (0:ℝ)..1, periodicWindowPulse eps s t C (x-a)) = (t-s)/C := by
  rw [intervalIntegral.integral_comp_sub_right _ a]
  have per := periodicWindowPulse_periodic eps s t C
  have ep := per.intervalIntegral_add_eq (0-a) (-(1/2:ℝ))
  rw [show (0:ℝ)-a+1=1-a by ring, show -(1/2:ℝ)+1=1/2 by norm_num] at ep
  rw [ep]
  have eq : EqOn (periodicWindowPulse eps s t C)
    (fun x => smoothedWindowPulse eps s t (C*x)) [[-(1/2:ℝ),1/2]] := by
    intro x hx
    rw [uIcc_of_le (by norm_num)] at hx
    exact periodic_pulse_equals_real_on_fundamental he hC hm hs ht hx
  rw [intervalIntegral.integral_congr eq, intervalIntegral.integral_eq_integral_of_support_subset]
  · rw [Measure.integral_comp_mul_left (smoothedWindowPulse eps s t) C,
      abs_of_pos (inv_pos.mpr hC),smoothedWindowPulse_integral he hst,smul_eq_mul,div_eq_mul_inv,mul_comm]
  · intro x hx
    have h := abs_le.mp (scaled_pulse_nonzero_support he hC hs ht hx)
    exact ⟨by linarith [h.1],by linarith [h.2]⟩

theorem periodicWindowPulse_intervalIntegrable (eps s t C a : ℝ) (he : 0 < eps) :
    IntervalIntegrable (fun x => periodicWindowPulse eps s t C (x-a)) volume 0 1 := by
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le (show (0:ℝ) ≤ 1 by norm_num)).2
  apply Measure.integrableOn_of_bounded (M:=1) (s_finite:=by simp [Real.volume_Ioc])
    (((periodicWindowPulse_measurable eps s t C).comp (measurable_id.sub_const a)).aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun x => by
    have h := smoothedWindowPulse_bounds (s:=s) (t:=t) (x:=C*centeredPeriodRep (x-a)) he
    change ‖smoothedWindowPulse eps s t (C*centeredPeriodRep (x-a))‖ ≤ (1:ℝ)
    rw [Real.norm_eq_abs,abs_of_nonneg h.1]
    exact h.2

/-- Exact mass of each of the local pulse families in the physical period. -/
theorem atomPulseTrain_mean {B K : ℕ} [NeZero K] (f : ZMod K → Fin B)
    {eps s t C M a : ℝ} (he : 0 < eps) (hC : 0 < C) (hm : M/C < 1/4)
    (hs : -M ≤ s-eps/2) (ht : t+eps/2 ≤ M) (hst : s ≤ t) :
    (∫ x in (0:ℝ)..1, atomPulseTrain f eps s t C a x) = (K:ℝ)*((t-s)/C) := by
  unfold atomPulseTrain
  rw [intervalIntegral.integral_finsetSum]
  · simp only [periodicWindowPulse_mean he hC hm hs ht hst, Finset.sum_const,
      Finset.card_univ,ZMod.card,nsmul_eq_mul]
  · intro j _
    exact periodicWindowPulse_intervalIntegrable _ _ _ _ _ he

#print axioms smoothedWindowPulse_reflect
#print axioms pulseOverlap_reflect_zero
#print axioms atomPulseTrain_mean

end CenteredCubeSqrt
