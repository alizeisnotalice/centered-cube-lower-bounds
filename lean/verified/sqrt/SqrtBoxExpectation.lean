import SqrtRawTranslationL2
import Mathlib.MeasureTheory.Integral.Prod

namespace CenteredCubeSqrt
open MeasureTheory Set
open scoped Interval
set_option maxHeartbeats 900000

noncomputable def unitPeriodMeasure : Measure ℝ := volume.restrict (Ioc 0 1)

noncomputable def centeredBoxMeasure (δ : ℝ) : Measure ℝ :=
  ENNReal.ofReal (1/δ) • volume.restrict (Ioc (-δ/2) (δ/2))

noncomputable def realSmoothed (μ : Measure ℝ) (F : ℝ→ℝ) (x : ℝ) :=
  ∫ z, F (x-z) ∂μ

theorem unitPeriodMeasure_isProbability : IsProbabilityMeasure unitPeriodMeasure :=
  ⟨by unfold unitPeriodMeasure; rw [Measure.restrict_apply_univ]; norm_num [Real.volume_Ioc]⟩

theorem centeredBoxMeasure_isProbability {δ : ℝ} (hδ : 0<δ) :
    IsProbabilityMeasure (centeredBoxMeasure δ) := by
  constructor
  unfold centeredBoxMeasure
  rw [smul_apply,Measure.restrict_apply_univ,Real.volume_Ioc,smul_eq_mul,
    show δ/2-(-δ/2)=δ by ring,←ENNReal.ofReal_mul (by positivity),one_div_mul_cancel hδ.ne',
    ENNReal.ofReal_one]

theorem centeredBoxMeasure_integral_as_interval {δ : ℝ} (hδ : 0<δ) (F : ℝ→ℝ) :
    (∫ z, F z ∂centeredBoxMeasure δ) = (1/δ)*(∫ z in -δ/2..δ/2,F z) := by
  unfold centeredBoxMeasure
  rw [integral_smul_measure,ENNReal.toReal_ofReal (by positivity),smul_eq_mul,
    intervalIntegral.integral_of_le (by linarith : -δ/2≤δ/2)]

theorem centeredBoxMeasure_ae_mem {δ : ℝ} :
    ∀ᵐ x ∂centeredBoxMeasure δ, x∈Icc (-δ/2) (δ/2) := by
  have H : ∀ᵐ x ∂(volume : Measure ℝ).restrict (Ioc (-δ/2) (δ/2)), x∈Ioc (-δ/2) (δ/2) :=
    ae_restrict_mem measurableSet_Ioc
  unfold centeredBoxMeasure
  exact Measure.ae_smul_measure (H.mono (fun _ h => Ioc_subset_Icc_self h)) _

theorem real_integrable_bounded {A : Type*} [MeasurableSpace A] (μ : Measure A) [IsFiniteMeasure μ]
    {F : A→ℝ} (hF : Measurable F) {K : ℝ} (hK : ∀ x,|F x|≤K) : Integrable F μ := by
  apply integrableOn_univ.mp
  apply Measure.integrableOn_of_bounded (M:=K) (s_finite:=(measure_lt_top μ univ).ne) hF.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hK x)

theorem realSmoothed_measurable {μ : Measure ℝ} [IsFiniteMeasure μ] {F : ℝ→ℝ}
    (hF : Measurable F) : Measurable (realSmoothed μ F) := by
  exact (hF.comp (measurable_fst.sub measurable_snd)).stronglyMeasurable.integral_prod_right'.measurable

theorem realSmoothed_abs_le {μ : Measure ℝ} [IsProbabilityMeasure μ] {F : ℝ→ℝ} {K : ℝ}
    (hK : ∀ x, |F x|≤K) (x : ℝ) : |realSmoothed μ F x|≤K := by
  have h := norm_integral_le_of_norm_le_const (μ:=μ) (f:=fun z => F (x-z)) (C:=K)
    (Filter.Eventually.of_forall (fun z => by simpa only [Real.norm_eq_abs] using hK (x-z)))
  simpa [realSmoothed,Real.norm_eq_abs] using h

noncomputable def shiftedPeriodGram (F G : ℝ→ℝ) (u v : ℝ) :=
    ∫ x, F (x-u)*G (x-v) ∂unitPeriodMeasure

theorem shiftedPeriodGram_eq_periodInner (F G : ℝ→ℝ) (u v : ℝ) :
    shiftedPeriodGram F G u v = periodInner (fun x => F (x-u)) (fun x => G (x-v)) := by
  unfold shiftedPeriodGram periodInner unitPeriodMeasure
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1)]

theorem shiftedPeriodGram_both_measurable {F G : ℝ→ℝ} (hF : Measurable F) (hG : Measurable G) :
    Measurable (fun uv : ℝ×ℝ => shiftedPeriodGram F G uv.1 uv.2) := by
  let : IsProbabilityMeasure unitPeriodMeasure := unitPeriodMeasure_isProbability
  have h : Measurable (fun z : (ℝ×ℝ)×ℝ => F (z.2-z.1.1)*G (z.2-z.1.2)) :=
    (hF.comp (measurable_snd.sub measurable_fst.fst)).mul
      (hG.comp (measurable_snd.sub measurable_fst.snd))
  exact h.stronglyMeasurable.integral_prod_right'.measurable

theorem shiftedPeriodGram_abs_le {F G : ℝ→ℝ} {A B : ℝ}
    (hF : ∀ x,|F x|≤A) (hG : ∀ x,|G x|≤B) (u v : ℝ) :
    |shiftedPeriodGram F G u v|≤A*B := by
  let : IsProbabilityMeasure unitPeriodMeasure := unitPeriodMeasure_isProbability
  have hA : 0≤A := (abs_nonneg _).trans (hF 0)
  have h := norm_integral_le_of_norm_le_const (μ:=unitPeriodMeasure)
    (f:=fun x => F (x-u)*G (x-v)) (C:=A*B)
    (Filter.Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs,abs_mul]
      exact mul_le_mul (hF _) (hG _) (abs_nonneg _) hA))
  simpa [shiftedPeriodGram,Real.norm_eq_abs] using h

theorem shiftedPeriodGram_diagonal {F G : ℝ→ℝ}
    (hF : Function.Periodic F 1) (hG : Function.Periodic G 1) (u : ℝ) :
    shiftedPeriodGram F G u u=periodInner F G := by
  rw [shiftedPeriodGram_eq_periodInner]
  unfold periodInner
  let Q (x : ℝ) := F x*G x
  have h : Function.Periodic Q 1 := hF.mul hG
  change (∫ x in (0:ℝ)..1,Q (x+ -u))=∫ x in (0:ℝ)..1,Q x
  rw [intervalIntegral.integral_comp_add_right,zero_add,add_comm (1:ℝ),h.intervalIntegral_add_eq (-u) 0,zero_add]

#print axioms shiftedPeriodGram_diagonal
#print axioms realSmoothed_measurable
end CenteredCubeSqrt
