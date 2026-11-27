import SqrtBoxGramIdentity
import SqrtSmoothedPrimitiveAverage
import UniformBoxDistance

namespace CenteredCubeSqrt
open MeasureTheory Set
open scoped Interval
set_option maxHeartbeats 1000000

theorem shifted_rawWindow_square_eq {B K : ℕ} [NeZero K] (f : ZMod K→Fin B)
    (L u v : ℝ) :
    (∫ x, (actualRawWindow f L (x-u)-actualRawWindow f L (x-v))^2 ∂unitPeriodMeasure) =
      ∫ x in (0:ℝ)..1, (actualRawWindow f L (x+(v-u))-actualRawWindow f L x)^2 := by
  let W := actualRawWindow f L
  let Q (x : ℝ) := (W (x+(v-u))-W x)^2
  have pW : Function.Periodic W 1 := actualRawWindow_periodic f L
  have hQ : Function.Periodic Q 1 := by
    intro x
    unfold Q
    rw [pW x,show x+1+(v-u)=x+(v-u)+1 by ring,pW (x+(v-u))]
  have e (x : ℝ) : (W (x-u)-W (x-v))^2 = Q (x+ -v) := by
    unfold Q
    rw [show x+ -v+(v-u)=x-u by ring,sub_eq_add_neg x v]
  change (∫ x,(W (x-u)-W (x-v))^2 ∂unitPeriodMeasure)=_
  simp_rw [e]
  unfold unitPeriodMeasure
  rw [←intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),
    intervalIntegral.integral_comp_add_right,zero_add,add_comm (1:ℝ),
    hQ.intervalIntegral_add_eq (-v) 0,zero_add]

theorem raw_shiftDifferenceGram_abs_le {B K : ℕ} [NeZero K] (f : ZMod K→Fin B)
    (L J u v : ℝ) (hK : (K:ℝ)*|v-u|≤1) :
    |shiftDifferenceGram (actualRawWindow f L) (actualRawWindow f J) u v|≤4*(K:ℝ)*|v-u| := by
  let : IsProbabilityMeasure unitPeriodMeasure := unitPeriodMeasure_isProbability
  let F (x : ℝ) := actualRawWindow f L (x-u)-actualRawWindow f L (x-v)
  let G (x : ℝ) := actualRawWindow f J (x-u)-actualRawWindow f J (x-v)
  have b {L' : ℝ} (x : ℝ) : |actualRawWindow f L' (x-u)-actualRawWindow f L' (x-v)|≤4 := by
    have h := abs_add_le (actualRawWindow f L' (x-u)) (-actualRawWindow f L' (x-v))
    rw [←sub_eq_add_neg,abs_neg] at h
    exact h.trans (by linarith [actualRawWindow_abs_le_two f L' (x-u),actualRawWindow_abs_le_two f L' (x-v)])
  have m (L' : ℝ) : Measurable (fun x => actualRawWindow f L' (x-u)-actualRawWindow f L' (x-v)) :=
    ((actualRawWindow_measurable f L').comp (measurable_id.sub measurable_const)).sub
      ((actualRawWindow_measurable f L').comp (measurable_id.sub measurable_const))
  have ints (L' : ℝ) : Integrable (fun x => (actualRawWindow f L' (x-u)-actualRawWindow f L' (x-v))^2)
      unitPeriodMeasure :=
    real_integrable_bounded _ ((m L').pow_const 2) (K:=16) (fun x => by
      rw [abs_of_nonneg (sq_nonneg _),←sq_abs]
      exact (pow_le_pow_left₀ (abs_nonneg _) (b (L':=L') x) 2).trans_eq (by norm_num))
  have f2 : Integrable (fun x => (F x)^2) unitPeriodMeasure := ints L
  have g2 : Integrable (fun x => (G x)^2) unitPeriodMeasure := ints J
  have p (x : ℝ) : ‖F x*G x‖ ≤ ((F x)^2+(G x)^2)/2 := by
    rw [Real.norm_eq_abs,abs_mul]
    nlinarith [sq_nonneg (|F x|-|G x|),sq_abs (F x),sq_abs (G x)]
  have E := norm_integral_le_of_norm_le ((f2.add g2).div_const 2) (Filter.Eventually.of_forall p)
  change |∫ x, F x*G x ∂unitPeriodMeasure|≤_
  rw [Real.norm_eq_abs,integral_div] at E
  simp only [Pi.add_apply] at E
  rw [integral_add f2 g2] at E
  refine E.trans ?_
  have h1 := rawWindow_both_sign_increment_L2 f L (v-u) hK
  have h2 := rawWindow_both_sign_increment_L2 f J (v-u) hK
  change ((∫ x, (actualRawWindow f L (x-u)-actualRawWindow f L (x-v))^2 ∂unitPeriodMeasure) +
    (∫ x, (actualRawWindow f J (x-u)-actualRawWindow f J (x-v))^2 ∂unitPeriodMeasure))/2≤_
  rw [shifted_rawWindow_square_eq,shifted_rawWindow_square_eq]
  linarith

theorem actual_atomic_box_gram_error {B K : ℕ} [NeZero K] (hB : 0<B) (hK : 2≤K)
    (f : ZMod K→Fin B) {δ : ℝ} (hδ0 : 0<δ) (hδ : δ<1/((B:ℝ)*K)) (hKδ : (K:ℝ)*δ≤1) (L J : ℝ) :
    |periodInner (actualRawWindow f L) (actualRawWindow f J) -
      periodInner (actualAtomicWindow f δ L) (actualAtomicWindow f δ J)|≤(2/3)*(K:ℝ)*δ := by
  let μ := centeredBoxMeasure δ
  let : IsProbabilityMeasure μ := centeredBoxMeasure_isProbability hδ0
  let F := actualRawWindow f L
  let G := actualRawWindow f J
  let Q := shiftDifferenceGram F G
  have hM : Measurable (fun uv : ℝ×ℝ => Q uv.1 uv.2) := by
    let : IsProbabilityMeasure unitPeriodMeasure := unitPeriodMeasure_isProbability
    have fM := actualRawWindow_measurable f L
    have gM := actualRawWindow_measurable f J
    have h : Measurable (fun z : (ℝ×ℝ)×ℝ => (F (z.2-z.1.1)-F (z.2-z.1.2))*
        (G (z.2-z.1.1)-G (z.2-z.1.2))) :=
      ((fM.comp (measurable_snd.sub measurable_fst.fst)).sub (fM.comp (measurable_snd.sub measurable_fst.snd))).mul
        ((gM.comp (measurable_snd.sub measurable_fst.fst)).sub (gM.comp (measurable_snd.sub measurable_fst.snd)))
    exact h.stronglyMeasurable.integral_prod_right'.measurable
  have hdom : ∀ᵐ t ∂μ, t∈Icc (-δ/2) (δ/2) := centeredBoxMeasure_ae_mem
  have hdom₂ : ∀ᵐ z ∂μ.prod μ, z.1∈Icc (-δ/2) (δ/2) ∧ z.2∈Icc (-δ/2) (δ/2) :=
    (Measure.ae_prod_iff_ae_ae (p:=fun z : ℝ×ℝ => z.1∈Icc (-δ/2) (δ/2) ∧ z.2∈Icc (-δ/2) (δ/2))
      ((measurable_fst measurableSet_Icc).inter (measurable_snd measurableSet_Icc))).mpr
      (hdom.mono (fun _ hx => hdom.mono (fun _ hy => ⟨hx,hy⟩)))
  have hDist : Integrable (fun p : ℝ×ℝ => 4*(K:ℝ)*|p.2-p.1|) (μ.prod μ) := by
    apply integrableOn_univ.mp
    have hM : Measurable (fun p : ℝ×ℝ => 4*(K:ℝ)*|p.2-p.1|) :=
      (continuous_const.mul (continuous_snd.sub continuous_fst).abs).measurable
    apply Measure.integrableOn_of_bounded (M:=4*(K:ℝ)*δ) (s_finite:=(measure_lt_top _ _).ne)
      hM.aestronglyMeasurable
    simp only [Measure.restrict_univ]
    filter_upwards [hdom₂] with p hp
    have e : |p.2-p.1|≤δ := abs_le.mpr ⟨by linarith [hp.1.2,hp.2.1],by linarith [hp.1.1,hp.2.2]⟩
    change ‖4*(K:ℝ)*|p.2-p.1|‖ ≤ 4*(K:ℝ)*δ
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity : 0≤4*(K:ℝ)*|p.2-p.1|)]
    exact mul_le_mul_of_nonneg_left e (by positivity : 0≤4*(K:ℝ))
  have hbound : ∀ᵐ p ∂μ.prod μ, ‖Q p.1 p.2‖ ≤ 4*(K:ℝ)*|p.2-p.1| := by
    filter_upwards [hdom₂] with p hp
    have e : |p.2-p.1|≤δ := abs_le.mpr ⟨by linarith [hp.1.2,hp.2.1],by linarith [hp.1.1,hp.2.2]⟩
    simpa only [Real.norm_eq_abs] using raw_shiftDifferenceGram_abs_le f L J p.1 p.2
      ((mul_le_mul_of_nonneg_left e (by positivity : 0≤(K:ℝ))).trans hKδ)
  have hI : Integrable (fun p : ℝ×ℝ => Q p.1 p.2) (μ.prod μ) := hDist.mono' hM.aestronglyMeasurable hbound
  have h := norm_integral_le_of_norm_le hDist hbound
  rw [integral_prod _ hI,integral_prod _ hDist,Real.norm_eq_abs] at h
  have ht := double_shiftDifferenceGram_identity (μ:=μ) (actualRawWindow_measurable f L)
    (actualRawWindow_measurable f J) (actualRawWindow_periodic f L) (actualRawWindow_periodic f J)
    (actualRawWindow_abs_le_two f L) (actualRawWindow_abs_le_two f J)
  change |(∫ u, ∫ v, Q u v ∂μ ∂μ)| ≤ _ at h
  rw [ht,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤2)] at h
  have he (P : ℝ) : realSmoothed μ (actualRawWindow f P)=actualAtomicWindow f δ P := by
    funext x
    unfold realSmoothed
    rw [centeredBoxMeasure_integral_as_interval hδ0]
    exact (actualAtomicWindow_is_box_average hB hK f hδ0 hδ P x).symm
  rw [he L,he J] at h
  have hE : (∫ u, ∫ v, (4*(K:ℝ)*|v-u|) ∂μ ∂μ) = 4*(K:ℝ)*(δ/3) := by
    simp_rw [integral_const_mul]
    congr 1
    have hswap (u : ℝ) : (∫ v, |v-u| ∂μ) = ∫ v, |u-v| ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun v => abs_sub_comm v u)
    simp_rw [hswap]
    change (∫ u, ∫ v, |u-v| ∂centeredBoxMeasure δ ∂centeredBoxMeasure δ) = _
    simp_rw [centeredBoxMeasure_integral_as_interval hδ0]
    rw [intervalIntegral.integral_const_mul,
      CubeSqrtEnd.integral_double_abs_sub_interval (by linarith : -δ/2≤δ/2),
      show δ/2-(-δ/2)=δ by ring]
    field_simp
  rw [hE] at h
  linarith

#print axioms actual_atomic_box_gram_error
end CenteredCubeSqrt
