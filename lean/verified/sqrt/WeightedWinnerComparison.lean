import GaussianFaceLayercake
import WeightedFaceError

open MeasureTheory ProbabilityTheory Set Filter CubeSqrtProbability
open scoped NNReal ENNReal Topology ProbabilityTheory
namespace CubeBrownian

noncomputable def winnerFaceWeight
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) (Z : Ω → ℝ) (D : Ω → E) (F : Set E) : ℝ :=
  (∫⁻ w in {w | 0 < Z w ∧ D w ∈ F}, ENNReal.ofReal (Real.exp (-(Z w))) ∂μ).toReal

theorem measurable_winner_window_real
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsFiniteMeasure μ] (Z : Ω → ℝ) (D : Ω → E)
    (hmZ : Measurable Z) (hmD : Measurable D) (F : Set E) (hF : MeasurableSet F) :
    Measurable (fun r ↦ μ.real (weightedWindow Z 0 r ∩ D ⁻¹' F)) := by
  let B : Set (ℝ × Ω) := {p | (0 < Z p.2 ∧ Z p.2 ≤ 0+p.1) ∧ D p.2 ∈ F}
  have h₁ : MeasurableSet {p : ℝ × Ω | 0 < Z p.2} :=
    measurableSet_lt measurable_const (hmZ.comp measurable_snd)
  have h₂ : MeasurableSet {p : ℝ × Ω | Z p.2 ≤ 0+p.1} :=
    measurableSet_le (hmZ.comp measurable_snd) (by fun_prop)
  have hB : MeasurableSet B := (h₁.inter h₂).inter ((hmD.comp measurable_snd) hF)
  exact (measurable_measure_prodMk_left (ν:=μ) hB).ennreal_toReal

theorem winner_face_weight_eq_window_integral
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : Ω → ℝ) (D : Ω → E)
    (hmZ : Measurable Z) (hmD : Measurable D) (F : Set E) (hF : MeasurableSet F) :
    winnerFaceWeight μ Z D F =
      ∫ r in Ioi (0:ℝ), Real.exp (-r)* μ.real (weightedWindow Z 0 r ∩ D ⁻¹' F) := by
  let V (r : ℝ) := μ (weightedWindow Z 0 r ∩ D ⁻¹' F)
  let A (r : ℝ) := Real.exp (-r)*(V r).toReal
  have hA : Measurable A := (Real.measurable_exp.comp measurable_neg).mul
    (measurable_winner_window_real μ Z D hmZ hmD F hF)
  have h0 (r : ℝ) : 0 ≤ A r := mul_nonneg (Real.exp_pos _).le ENNReal.toReal_nonneg
  have hE (r : ℝ) : ENNReal.ofReal (A r) = expTailWeight r*V r := by
    unfold A expTailWeight
    rw [ENNReal.ofReal_mul (Real.exp_pos _).le,ENNReal.ofReal_toReal (measure_ne_top _ _)]
  have hSupp (r : ℝ) (hr : r ∉ Ioi (0:ℝ)) : expTailWeight r*V r = 0 := by
    have h : weightedWindow Z 0 r = ∅ := by
      apply eq_empty_iff_forall_notMem.2
      intro x hx
      have h1 : 0 < Z x := hx.1
      have h2 : Z x ≤ r := by simpa only [zero_add] using hx.2
      exact hr (h1.trans_le h2)
    simp [V,h]
  have hI : (∫⁻ r : ℝ, expTailWeight r*V r) = ∫⁻ r in Ioi (0:ℝ), ENNReal.ofReal (A r) := by
    rw [← lintegral_indicator measurableSet_Ioi]
    apply lintegral_congr
    intro r
    by_cases hr : r ∈ Ioi (0:ℝ)
    · rw [indicator_of_mem hr,hE]
    · rw [indicator_of_notMem hr,hSupp r hr]
  unfold winnerFaceWeight
  rw [gaussian_face_layercake μ Z D hmZ hmD F hF]
  change (∫⁻ r : ℝ, expTailWeight r*V r).toReal = ∫ r in Ioi (0:ℝ), A r
  rw [hI]
  exact (integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall h0) hA.aestronglyMeasurable).symm

/-- Uniform finite-window probability comparison transfers to the exact winner
thin-layer weight, without any loss depending on the threshold. -/
theorem weighted_winner_face_comparison
    {Ω Ω' E E' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace E] [MeasurableSpace E']
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure Ω') [IsProbabilityMeasure ν]
    (Z : Ω → ℝ) (D : Ω → E) (Z' : Ω' → ℝ) (D' : Ω' → E')
    (hmZ : Measurable Z) (hmD : Measurable D) (hmZ' : Measurable Z') (hmD' : Measurable D')
    (F : Set E) (F' : Set E') (hF : MeasurableSet F) (hF' : MeasurableSet F')
    (ε : ℝ) (hE : ∀ r > 0,
      |μ.real (weightedWindow Z 0 r ∩ D ⁻¹' F) - ν.real (weightedWindow Z' 0 r ∩ D' ⁻¹' F')| ≤ ε) :
    |winnerFaceWeight μ Z D F - winnerFaceWeight ν Z' D' F'| ≤ ε := by
  rw [winner_face_weight_eq_window_integral μ Z D hmZ hmD F hF,
    winner_face_weight_eq_window_integral ν Z' D' hmZ' hmD' F' hF']
  exact exp_weighted_Ioi_comparison _ _ ε (measurable_winner_window_real μ Z D hmZ hmD F hF)
    (measurable_winner_window_real ν Z' D' hmZ' hmD' F' hF')
    (fun r ↦ by rw [abs_of_nonneg measureReal_nonneg]; exact measureReal_le_one)
    (fun r ↦ by rw [abs_of_nonneg measureReal_nonneg]; exact measureReal_le_one)
    hE

end CubeBrownian
#print axioms CubeBrownian.weighted_winner_face_comparison
