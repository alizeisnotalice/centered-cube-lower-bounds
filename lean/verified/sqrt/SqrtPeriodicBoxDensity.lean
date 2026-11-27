import SqrtPulseTrainMeans

namespace CenteredCubeSqrt

open MeasureTheory Set
open scoped BigOperators Interval
open Classical

/-- Actual shifted box density on the real period-one lift. -/
noncomputable def periodicBoxDensity (delta a x : ℝ) : ℝ :=
  boxWindowDensity delta (centeredPeriodRep (x-a))

theorem boxWindowDensity_even (eps x : ℝ) : boxWindowDensity eps (-x) = boxWindowDensity eps x := by
  have he : -x ∈ Icc (-eps/2) (eps/2) ↔ x ∈ Icc (-eps/2) (eps/2) := by
    simp only [mem_Icc]
    exact ⟨fun h => ⟨by linarith [h.2],by linarith [h.1]⟩,
      fun h => ⟨by linarith [h.2],by linarith [h.1]⟩⟩
  unfold boxWindowDensity
  simp [indicator_apply, he]

theorem boxWindowDensity_of_far {delta x : ℝ} (h : delta/2 < |x|) :
    boxWindowDensity delta x = 0 := by
  apply Set.indicator_of_notMem
  exact fun hm => h.not_ge (abs_le.mpr ⟨by linarith [hm.1],hm.2⟩)

theorem boxWindowDensity_scale {eps C x : ℝ} (hC : 0 < C) :
    boxWindowDensity (eps/C) x = C*boxWindowDensity eps (C*x) := by
  have he : x ∈ Icc (-(eps/C)/2) (eps/C/2) ↔ C*x ∈ Icc (-eps/2) (eps/2) := by
    have eq1 : -(eps/C)/2 = (-eps/2)/C := by field_simp
    have eq2 : eps/C/2 = (eps/2)/C := by field_simp
    simp only [mem_Icc,eq1,eq2,div_le_iff₀ hC,le_div_iff₀ hC]
    rw [mul_comm x C]
  unfold boxWindowDensity
  by_cases hx : C*x∈Icc (-eps/2) (eps/2)
  · rw [indicator_of_mem (he.mpr hx),indicator_of_mem hx]
    field_simp
  · rw [indicator_of_notMem (fun h => hx (he.mp h)),indicator_of_notMem hx,mul_zero]

theorem periodicBoxDensity_measurable (delta a : ℝ) :
    Measurable (periodicBoxDensity delta a) := by
  have hfloor : Measurable (fun x : ℝ => (⌊x-a+1/2⌋:ℝ)) :=
    (Measurable.of_discrete (f:=fun z:ℤ => (z:ℝ))).comp <|
      ((measurable_id.sub_const a).add_const (1/2:ℝ)).floor
  unfold periodicBoxDensity centeredPeriodRep boxWindowDensity
  exact (measurable_const.indicator measurableSet_Icc).comp ((measurable_id.sub_const a).sub hfloor)

theorem periodicBoxDensity_intervalIntegrable (delta a c d : ℝ) (hδ : 0 < delta) :
    IntervalIntegrable (periodicBoxDensity delta a) volume c d := by
  rw [intervalIntegrable_iff]
  apply Measure.integrableOn_of_bounded (M:=1/delta) (s_finite:=by rw [uIoc]; simp [Real.volume_Ioc])
    (periodicBoxDensity_measurable delta a).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro x
  unfold periodicBoxDensity boxWindowDensity
  by_cases hx : centeredPeriodRep (x-a) ∈ Icc (-delta/2) (delta/2)
  · rw [indicator_of_mem hx,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  · rw [indicator_of_notMem hx,norm_zero]
    positivity

theorem smoothedWindowPulse_as_box_integral {eps s t z : ℝ} (hst : s ≤ t) :
    smoothedWindowPulse eps s t z = ∫ y in s..t, boxWindowDensity eps (z-y) := by
  unfold smoothedWindowPulse
  rw [MeasureTheory.convolution_def,intervalIntegral.integral_of_le hst]
  change (∫ x : ℝ, realIntervalIndicator s t x*boxWindowDensity eps (z-x)) = _
  have eq (x : ℝ) : realIntervalIndicator s t x*boxWindowDensity eps (z-x) =
      (Icc s t).indicator (fun y => boxWindowDensity eps (z-y)) x := by
    unfold realIntervalIndicator
    by_cases h : x∈Icc s t <;> simp [h]
  simp_rw [eq,integral_indicator measurableSet_Icc]
  exact setIntegral_congr_set Ioc_ae_eq_Icc.symm

/-- Actual periodic box mass on a local interval of length
(t−s)/C equals the reflected periodized smoothed pulse exactly. -/
theorem periodicBoxDensity_small_interval {eps C T s t a c : ℝ}
    (he : 0 < eps) (hC : 0 < C) (hT : 0 ≤ T) (hlarge : (T+eps/2)/C < 1/4)
    (hs : -T ≤ s) (hst : s ≤ t) (ht : t ≤ T) :
    (∫ x in c+s/C..c+t/C, periodicBoxDensity (eps/C) a x) =
      periodicWindowPulse eps (-t) (-s) C (c-a) := by
  let z := centeredPeriodRep (c-a)
  have hz : |z| ≤ 1/2 := by
    have h := centeredPeriodRep_range (c-a)
    exact abs_le.mpr ⟨h.1,h.2.le⟩
  have hε : eps/C/2 < 1/4 := by
    have e : eps/C/2 = (eps/2)/C := by field_simp
    rw [e]
    exact (div_le_div_of_nonneg_right (by linarith) hC.le).trans_lt hlarge
  have hint := intervalIntegral.smul_integral_comp_mul_add
    (a:=s) (b:=t) (periodicBoxDensity (eps/C) a) (1/C) c
  rw [smul_eq_mul,show 1/C*s+c=c+s/C by ring,show 1/C*t+c=c+t/C by ring] at hint
  rw [← hint]
  have hu (u : ℝ) (hu : u∈Icc s t) :
      periodicBoxDensity (eps/C) a (1/C*u+c) = C*boxWindowDensity eps (C*z+u) := by
    have huf : |u/C| ≤ 1/4 := by
      rw [abs_div,abs_of_pos hC]
      exact (div_le_div_of_nonneg_right (abs_le.mpr ⟨hs.trans hu.1,hu.2.trans ht⟩) hC.le).trans
        ((div_le_div_of_nonneg_right (by linarith [he]) hC.le).trans hlarge.le)
    have hzu : |z+u/C| ≤ 3/4 := (abs_add_le _ _).trans (by linarith)
    have erep : centeredPeriodRep (1/C*u+c-a) = centeredPeriodRep (z+u/C) := by
      have eq : 1/C*u+c-a = (z+u/C)+(⌊c-a+1/2⌋:ℤ) := by dsimp [z,centeredPeriodRep]; ring
      rw [eq,centeredPeriodRep_int]
    unfold periodicBoxDensity
    rw [erep,← show C*(z+u/C)=C*z+u by field_simp,← boxWindowDensity_scale hC]
    rcases centeredPeriodRep_eq_or_shift hzu with h | ⟨h,hl⟩ | ⟨h,hh⟩
    · rw [h]
    · rw [h,boxWindowDensity_of_far,boxWindowDensity_of_far]
      · rw [abs_of_nonneg (by linarith)]
        linarith
      · rw [abs_of_nonpos (by linarith [(abs_le.mp hzu).2])]
        linarith [(abs_le.mp hzu).2]
    · rw [h,boxWindowDensity_of_far,boxWindowDensity_of_far]
      · rw [abs_of_nonpos (by linarith)]
        linarith
      · rw [abs_of_nonneg (by linarith [(abs_le.mp hzu).1])]
        linarith [(abs_le.mp hzu).1]
  rw [intervalIntegral.integral_congr (f:=fun u => periodicBoxDensity (eps/C) a (1/C*u+c))
    (g:=fun u => C*boxWindowDensity eps (C*z+u)) (fun u h => hu u (by rwa [uIcc_of_le hst] at h))]
  rw [intervalIntegral.integral_const_mul]
  have hmul : (1/C)* (C*(∫ u in s..t, boxWindowDensity eps (C*z+u))) =
      ∫ u in s..t, boxWindowDensity eps (C*z+u) := by field_simp
  rw [hmul,periodicWindowPulse,smoothedWindowPulse_reflect,smoothedWindowPulse_as_box_integral hst]
  apply intervalIntegral.integral_congr
  intro u _
  change boxWindowDensity eps (C*z+u) = boxWindowDensity eps (-(C*z)-u)
  rw [show -(C*z)-u=-(C*z+u) by ring,boxWindowDensity_even]

#print axioms periodicBoxDensity_small_interval

end CenteredCubeSqrt
