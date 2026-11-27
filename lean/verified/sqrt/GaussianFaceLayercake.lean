import GaussianFaceKernel
import WeightedTail

open MeasureTheory ProbabilityTheory Set Filter CubeSqrtProbability
open scoped NNReal ENNReal Topology ProbabilityTheory
namespace CubeBrownian

/-- The exact event used in Gaussian winner limits has the same weighted
window form as the finite-face Berry–Esseen bound. -/
theorem gaussian_face_layercake
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : Ω → ℝ) (D : Ω → E)
    (hmZ : Measurable Z) (hmD : Measurable D) (F : Set E) (hF : MeasurableSet F) :
    (∫⁻ w in {w | 0 < Z w ∧ D w ∈ F}, ENNReal.ofReal (Real.exp (-(Z w))) ∂μ) =
      ∫⁻ r : ℝ, expTailWeight r * μ (weightedWindow Z 0 r ∩ D ⁻¹' F) := by
  let S := D ⁻¹' F
  have hZplus : MeasurableSet {w | 0 < Z w} := measurableSet_lt measurable_const hmZ
  have h := weighted_tail_layercake (μ.restrict S) hmZ 0
  rw [Measure.restrict_restrict hZplus] at h
  simp_rw [Measure.restrict_apply (weightedWindow_measurable hmZ 0 _),sub_zero] at h
  exact h

end CubeBrownian
#print axioms CubeBrownian.gaussian_face_layercake
