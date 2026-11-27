import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Tilted

open MeasureTheory Set
open scoped ENNReal
namespace CubeSqrtProbability

noncomputable def expTailWeight (r : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-r))

theorem expTailWeight_measurable : Measurable expTailWeight :=
  (Real.continuous_exp.comp continuous_neg).measurable.ennreal_ofReal

def weightedWindow {Ω : Type*} (S : Ω → ℝ) (h r : ℝ) : Set Ω :=
  {w | h < S w ∧ S w ≤ h+r}

theorem weightedWindow_measurable {Ω : Type*} [MeasurableSpace Ω] {S : Ω → ℝ}
    (hS : Measurable S) (h r : ℝ) : MeasurableSet (weightedWindow S h r) :=
  (measurableSet_lt measurable_const hS).inter (measurableSet_le hS measurable_const)

theorem expTailWeight_integral_Ici (a : ℝ) :
    (∫⁻ r in Ici a, expTailWeight r) = expTailWeight a := by
  rw [← Measure.restrict_congr_set (μ := (volume : Measure ℝ)) (Ioi_ae_eq_Ici (a := a))]
  unfold expTailWeight
  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_exp_neg_Ioi a)
    (ae_of_all _ fun r ↦ (Real.exp_pos (-r)).le), integral_exp_neg_Ioi]

theorem weighted_tail_layercake {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SFinite μ]
    {S : Ω → ℝ} (hS : Measurable S) (h : ℝ) :
    (∫⁻ w in {w | h < S w}, expTailWeight (S w-h) ∂μ) =
      ∫⁻ r : ℝ, expTailWeight r * μ (weightedWindow S h r) := by
  let D : Set (Ω × ℝ) := {p | h < S p.1 ∧ S p.1 ≤ h + p.2}
  have hD : MeasurableSet D :=
    (measurableSet_lt measurable_const (hS.comp measurable_fst)).inter
       (measurableSet_le (hS.comp measurable_fst) (measurable_const.add measurable_snd))
  let F (w : Ω) (r : ℝ) := D.indicator (fun p ↦ expTailWeight p.2) (w,r)
  have hF : Measurable (Function.uncurry F) :=
    (expTailWeight_measurable.comp measurable_snd).indicator hD
  have hleft (w : Ω) : (∫⁻ r, F w r) =
      {w | h < S w}.indicator (fun w ↦ expTailWeight (S w-h)) w := by
    by_cases hw : h < S w
    · have he : F w = (Ici (S w-h)).indicator expTailWeight := by
        funext r
        by_cases hr : S w-h ≤ r
        · have hwr : S w ≤ h+r := by linarith
          simp [F,D,hw,hr,hwr]
        · have hwr : ¬ S w ≤ h+r := by linarith
          simp [F,D,hw,hr,hwr]
      rw [he,lintegral_indicator measurableSet_Ici,expTailWeight_integral_Ici]
      simp [hw]
    · have he : F w = 0 := by funext r; simp [F,D,hw]
      simp [he,hw]
  have hright (r : ℝ) : (∫⁻ w, F w r ∂μ) =
      expTailWeight r * μ (weightedWindow S h r) := by
    have he : (fun w ↦ F w r) = (weightedWindow S h r).indicator
        (fun _ ↦ expTailWeight r) := by
      funext w
      by_cases hw : w ∈ weightedWindow S h r
      · have hd : (w,r) ∈ D := hw
        simp [F,hd,hw]
      · have hd : (w,r) ∉ D := hw
        simp [F,hd,hw]
    rw [he,lintegral_indicator (weightedWindow_measurable hS h r),
      lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter]
  have hs := lintegral_lintegral_swap (μ := μ) (ν := volume) hF.aemeasurable
  simp_rw [hleft,hright] at hs
  rwa [lintegral_indicator (measurableSet_lt measurable_const hS)] at hs

end CubeSqrtProbability
#print axioms CubeSqrtProbability.weighted_tail_layercake
