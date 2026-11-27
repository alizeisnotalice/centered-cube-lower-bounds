import SmoothFaceCutoff
import PolyhedralStrips

open Set MeasureTheory ProbabilityTheory
open scoped NNReal

namespace CubeSqrtProbability

theorem measurableSet_faceEvent {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (Y : Ω → ι → ℝ) (hY : ∀ i, Measurable (fun w ↦ Y w i))
    (strict : ι → Bool) (c : ι → ℝ) (t : ℝ) :
    MeasurableSet (faceEvent Y strict c t) := by
  have he : faceEvent Y strict c t =
      ⋂ i, {w | facePass (strict i) (Y w i) (c i+t)} := by ext w; simp [faceEvent]
  rw [he]
  apply MeasurableSet.iInter
  intro i
  cases h : strict i
  · exact by simpa [facePass,h] using (measurableSet_le (hY i) measurable_const)
  · exact by simpa [facePass,h] using (measurableSet_lt (hY i) measurable_const)

theorem smooth_face_integral_sandwich {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → ι → ℝ)
    (hY : ∀ i, Measurable (fun w ↦ Y w i)) (strict : ι → Bool)
    (c : ι → ℝ) (t : ℝ) {η : ℝ} (hη : 0 < η) :
    μ.real (faceEvent Y strict c t) ≤ ∫ w, smoothFaceCutoff c t η (Y w) ∂μ ∧
      (∫ w, smoothFaceCutoff c t η (Y w) ∂μ) ≤
        μ.real (faceEvent Y strict c (t+η)) := by
  let f := fun w ↦ smoothFaceCutoff c t η (Y w)
  have hm : Measurable f :=
    (smoothFaceCutoff_contDiff c t η).continuous.measurable.comp (Measurable.of_eval hY)
  have hf : Integrable f μ := (integrable_const (1:ℝ)).mono' hm.aestronglyMeasurable
    (ae_of_all _ fun w ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (smoothFaceCutoff_nonneg c t η (Y w))]
      exact smoothFaceCutoff_le_one c t η (Y w))
  have hI (r : ℝ) : Integrable ((faceEvent Y strict c r).indicator (fun _ ↦ (1:ℝ))) μ :=
    (integrable_const (1:ℝ)).indicator (measurableSet_faceEvent Y hY strict c r)
  have hEval (r : ℝ) :
      (∫ w, (faceEvent Y strict c r).indicator (fun _ ↦ (1:ℝ)) w ∂μ) =
        μ.real (faceEvent Y strict c r) := by
    rw [integral_indicator (measurableSet_faceEvent Y hY strict c r), setIntegral_const, smul_eq_mul, mul_one]
  rw [← hEval t,← hEval (t+η)]
  constructor
  · refine integral_mono (hI t) hf (fun w ↦ ?_)
    by_cases hw : w ∈ faceEvent Y strict c t
    · rw [Set.indicator_of_mem hw]
      exact (smoothFaceCutoff_eq_one_of_mem strict c t hη hw).ge
    · rw [Set.indicator_of_notMem hw]
      exact smoothFaceCutoff_nonneg c t η (Y w)
  · refine integral_mono hf (hI (t+η)) (fun w ↦ ?_)
    by_cases hw : w ∈ faceEvent Y strict c (t+η)
    · rw [Set.indicator_of_mem hw]
      exact smoothFaceCutoff_le_one c t η (Y w)
    · rw [Set.indicator_of_notMem hw]
      exact (smoothFaceCutoff_eq_zero_of_not_mem strict c t hη hw).le

/-- A uniform comparison of smooth expectations suffices for all thresholds of
mixed open/closed face events, even for a singular joint Gaussian, provided
each scalar face has positive variance. -/
theorem smooth_face_comparison {Ω Ω' ι : Type*} [Fintype ι]
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure Ω') [IsProbabilityMeasure ν]
    (X : Ω → ι → ℝ) (G : Ω' → ι → ℝ)
    (hX : ∀ i, Measurable (fun w ↦ X w i))
    (hG : ∀ i, Measurable (fun w ↦ G w i))
    (strict : ι → Bool) (c m : ι → ℝ) (v : ι → ℝ≥0)
    (hv : ∀ i, v i ≠ 0)
    (hLaw : ∀ i, ν.map (fun w ↦ G w i) = gaussianReal (m i) (v i))
    {η : ℝ} (hη : 0 < η) (δ : ℝ)
    (hc : ∀ t, |(∫ w, smoothFaceCutoff c t η (X w) ∂μ) -
                 ∫ w, smoothFaceCutoff c t η (G w) ∂ν| ≤ δ) :
    |μ.real (faceEvent X strict c 0) - ν.real (faceEvent G strict c 0)| ≤
       δ + η * ∑ i, (√(2*Real.pi*(v i:ℝ)))⁻¹ := by
  have hx0 := smooth_face_integral_sandwich μ X hX strict c 0 hη
  have hg0 := smooth_face_integral_sandwich ν G hG strict c 0 hη
  have hxn := smooth_face_integral_sandwich μ X hX strict c (-η) hη
  have hgn := smooth_face_integral_sandwich ν G hG strict c (-η) hη
  have hsU := gaussian_face_event_strip_gain ν G strict c m v hv hG hLaw
    (t := 0) (u := η) hη.le
  have hsL := gaussian_face_event_strip_gain ν G strict c m v hv hG hLaw
    (t := -η) (u := 0) (by linarith)
  simp only [zero_add,neg_add_cancel] at hx0 hg0 hxn hgn
  simp only [sub_zero,zero_sub,neg_neg] at hsU hsL
  have hb0 := (abs_le.mp (hc 0)).2
  have hbn := (abs_le.mp (hc (-η))).1
  exact abs_le.mpr ⟨by linarith [hxn.2,hgn.1],by linarith [hx0.1,hg0.2]⟩

end CubeSqrtProbability
#print axioms CubeSqrtProbability.smooth_face_comparison
