import SqrtBoxExpectation

namespace CenteredCubeSqrt
open MeasureTheory Set
open scoped Interval
set_option maxHeartbeats 1000000

theorem shiftedPeriodGram_swap (F G : ℝ→ℝ) (u v : ℝ) :
    shiftedPeriodGram F G u v=shiftedPeriodGram G F v u := by
  unfold shiftedPeriodGram
  simp only [mul_comm]

theorem double_shiftedGram_is_smoothed {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {F G : ℝ→ℝ} (hF : Measurable F) (hG : Measurable G)
    {A B : ℝ} (bF : ∀ x, |F x|≤A) (bG : ∀ x, |G x|≤B) :
    (∫ u, ∫ v, shiftedPeriodGram F G u v ∂μ ∂μ) =
      periodInner (realSmoothed μ F) (realSmoothed μ G) := by
  let : IsProbabilityMeasure unitPeriodMeasure := unitPeriodMeasure_isProbability
  have hA : 0≤A := (abs_nonneg _).trans (bF 0)
  have bnd (x y : ℝ) : |F x*G y|≤A*B := by
    rw [abs_mul]
    exact mul_le_mul (bF _) (bG _) (abs_nonneg _) hA
  have e (u : ℝ) : (∫ v, shiftedPeriodGram F G u v ∂μ) =
      ∫ x, F (x-u)*realSmoothed μ G x ∂unitPeriodMeasure := by
    let hf (v x : ℝ) := F (x-u)*G (x-v)
    have hM : Measurable (Function.uncurry hf) :=
      (hF.comp (measurable_snd.sub measurable_const)).mul (hG.comp (measurable_snd.sub measurable_fst))
    have hInt := real_integrable_bounded (μ.prod unitPeriodMeasure) hM (fun x => bnd (x.2-u) (x.2-x.1))
    unfold shiftedPeriodGram
    rw [integral_integral_swap hInt]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun x => integral_const_mul _ _)
  simp_rw [e]
  let hf' (u x : ℝ) := F (x-u)*realSmoothed μ G x
  have hM' : Measurable (Function.uncurry hf') :=
    (hF.comp (measurable_snd.sub measurable_fst)).mul ((realSmoothed_measurable hG).comp measurable_snd)
  have hB' (x : ℝ) : |realSmoothed μ G x| ≤ B := realSmoothed_abs_le bG x
  have hBnd (z : ℝ×ℝ) : |Function.uncurry hf' z| ≤ A*B := by
    change |F (z.2-z.1)*realSmoothed μ G z.2|≤_
    rw [abs_mul]
    exact mul_le_mul (bF _) (hB' _) (abs_nonneg _) hA
  have hInt' := real_integrable_bounded (μ.prod unitPeriodMeasure) hM' hBnd
  rw [integral_integral_swap hInt']
  unfold periodInner unitPeriodMeasure
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => integral_mul_const _ _)

noncomputable def shiftDifferenceGram (F G : ℝ→ℝ) (u v : ℝ) :=
    ∫ x, (F (x-u)-F (x-v))*(G (x-u)-G (x-v)) ∂unitPeriodMeasure

theorem shiftDifferenceGram_expand {F G : ℝ→ℝ} (hF : Measurable F) (hG : Measurable G)
    {A B : ℝ} (bF : ∀ x, |F x|≤A) (bG : ∀ x, |G x|≤B) (u v : ℝ) :
    shiftDifferenceGram F G u v =
      shiftedPeriodGram F G u u - shiftedPeriodGram F G u v -
      (shiftedPeriodGram F G v u - shiftedPeriodGram F G v v) := by
  let : IsProbabilityMeasure unitPeriodMeasure := unitPeriodMeasure_isProbability
  have hA : 0≤A := (abs_nonneg _).trans (bF 0)
  have hInt (s t : ℝ) : Integrable (fun x => F (x-s)*G (x-t)) unitPeriodMeasure :=
    real_integrable_bounded _ ((hF.comp (measurable_id.sub measurable_const)).mul
        (hG.comp (measurable_id.sub measurable_const)))
      (fun x => by rw [abs_mul]; exact mul_le_mul (bF _) (bG _) (abs_nonneg _) hA)
  unfold shiftDifferenceGram shiftedPeriodGram
  have he (x : ℝ) : (F (x-u)-F (x-v))*(G (x-u)-G (x-v)) =
    (F (x-u)*G (x-u)-F (x-u)*G (x-v))-(F (x-v)*G (x-u)-F (x-v)*G (x-v)) := by ring
  simp_rw [he]
  have ih1 : Integrable (fun x => F (x-u)*G (x-u)-F (x-u)*G (x-v)) unitPeriodMeasure :=
    (hInt u u).sub (hInt u v)
  have ih2 : Integrable (fun x => F (x-v)*G (x-u)-F (x-v)*G (x-v)) unitPeriodMeasure :=
    (hInt v u).sub (hInt v v)
  rw [integral_sub ih1 ih2,integral_sub (hInt u u) (hInt u v),integral_sub (hInt v u) (hInt v v)]

theorem double_shiftDifferenceGram_identity {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {F G : ℝ→ℝ} (hF : Measurable F) (hG : Measurable G)
    (pF : Function.Periodic F 1) (pG : Function.Periodic G 1)
    {A B : ℝ} (bF : ∀ x, |F x|≤A) (bG : ∀ x, |G x|≤B) :
    (∫ u, ∫ v, shiftDifferenceGram F G u v ∂μ ∂μ) =
      2*(periodInner F G-periodInner (realSmoothed μ F) (realSmoothed μ G)) := by
  let C := periodInner F G
  let U (p : ℝ×ℝ) := shiftedPeriodGram F G p.1 p.2
  let V (p : ℝ×ℝ) := shiftedPeriodGram F G p.2 p.1
  let Q (p : ℝ×ℝ) := shiftDifferenceGram F G p.1 p.2
  have e : Q=fun p => (C-U p)-(V p-C) := by
    funext p
    unfold Q
    rw [shiftDifferenceGram_expand hF hG bF bG,shiftedPeriodGram_diagonal pF pG p.1,
      shiftedPeriodGram_diagonal pF pG p.2]
  have I : Integrable U (μ.prod μ) :=
    real_integrable_bounded _ (shiftedPeriodGram_both_measurable hF hG)
      (fun p => shiftedPeriodGram_abs_le bF bG p.1 p.2)
  have J : Integrable V (μ.prod μ) := I.swap
  have IC : Integrable (fun _ : ℝ×ℝ => C) (μ.prod μ) := integrable_const C
  have IQ : Integrable Q (μ.prod μ) := by rw [e]; exact (IC.sub I).sub (J.sub IC)
  have eq1 : (∫ p, U p ∂μ.prod μ)=periodInner (realSmoothed μ F) (realSmoothed μ G) := by
    rw [integral_prod _ I]
    exact double_shiftedGram_is_smoothed hF hG bF bG
  have eq2 : (∫ p, V p ∂μ.prod μ)=periodInner (realSmoothed μ F) (realSmoothed μ G) := by
    rw [integral_prod _ J]
    have e' (u v : ℝ) : V (u,v)=shiftedPeriodGram G F u v :=
      shiftedPeriodGram_swap F G v u
    simp_rw [e']
    rw [double_shiftedGram_is_smoothed hG hF bG bF]
    simp only [periodInner,mul_comm]
  change (∫ u, ∫ v, Q (u,v) ∂μ ∂μ)=_
  have IC₁ : Integrable (fun p => C-U p) (μ.prod μ) := IC.sub I
  have IC₂ : Integrable (fun p => V p-C) (μ.prod μ) := J.sub IC
  rw [←integral_prod _ IQ,e,integral_sub IC₁ IC₂,integral_sub IC I,integral_sub J IC,eq1,eq2]
  simp only [integral_const,probReal_univ,one_smul,C]
  ring

#print axioms double_shiftedGram_is_smoothed
#print axioms double_shiftDifferenceGram_identity
end CenteredCubeSqrt
