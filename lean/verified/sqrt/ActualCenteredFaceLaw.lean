import ActualFaceEncoding
import TrueTiltLimits

open MeasureTheory ProbabilityTheory Filter
namespace CubeSqrtProbability

/-- Push forward genuinely centered bounded coordinate facets; no start
assumption on dependence across individual faces is required. -/
theorem centered_facet_coordinate_law
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (G : Ω → ι → ℝ) (hG : Measurable G)
    (B : ℝ) (hB : 0 ≤ B) (hb : ∀ w i, |G w i| ≤ B) :
    let m (i : ι) := ∫ w, G w i ∂Q
    let A (w : Ω) (i : ι) := G w i - m i
    let μ := Q.map A
    Measurable A ∧ (∀ᵐ d ∂μ, ‖d‖ ≤ 2*B) ∧ (∀ i, (∫ d, d i ∂μ)=0) := by
  dsimp only
  let m (i : ι) := ∫ w, G w i ∂Q
  let A (w : Ω) (i : ι) := G w i - m i
  have hmG (i : ι) : Measurable (fun w ↦ G w i) := (measurable_pi_apply i).comp hG
  have hmA : Measurable A := Measurable.of_eval fun i ↦ (hmG i).sub measurable_const
  refine ⟨hmA, ?_, ?_⟩
  · rw [ae_map_iff hmA.aemeasurable (measurableSet_le continuous_norm.measurable measurable_const)]
    refine Eventually.of_forall fun w ↦ (pi_norm_le_iff_of_nonneg (by linarith)).2 fun i ↦ ?_
    rw [Real.norm_eq_abs]
    have hmi : |m i| ≤ B := by
      change ‖∫ w, G w i ∂Q‖ ≤ B
      have hbQ : ∀ᵐ w ∂Q, ‖G w i‖ ≤ B := ae_of_all Q fun w ↦ by simpa [Real.norm_eq_abs] using hb w i
      simpa using norm_integral_le_of_norm_le_const hbQ
    exact (abs_sub _ _).trans (by linarith [hb w i])
  · intro i
    rw [integral_map hmA.aemeasurable (measurable_pi_apply i).aestronglyMeasurable]
    change (∫ w, G w i - m i ∂Q)=0
    rw [integral_sub (integrable_of_uniform_abs Q (hmG i) (fun w ↦ hb w i)) (integrable_const _)]
    simp [m]

end CubeSqrtProbability
#print axioms CubeSqrtProbability.centered_facet_coordinate_law
