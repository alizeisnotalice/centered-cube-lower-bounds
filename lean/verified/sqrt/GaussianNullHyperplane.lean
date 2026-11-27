import GaussianWeakFaces

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology ProbabilityTheory
namespace CubeBrownian

/-- A nondegenerate scalar projection of a Gaussian vector has null level
sets, even when the ambient Gaussian law is singular. -/
theorem gaussian_measure_null_hyperplane
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (μ : Measure Ω) (Y : Ω → E) (hY : HasGaussianLaw Y μ)
    (L : StrongDual ℝ E) (hv : 0 < Var[L ∘ Y; μ]) (x : ℝ) :
    (μ.map Y) ((L : E → ℝ) ⁻¹' {x}) = 0 := by
  have hL : Measurable L := L.continuous.measurable
  rw [← Measure.map_apply hL (measurableSet_singleton x),
    AEMeasurable.map_map_of_aemeasurable hL.aemeasurable hY.aemeasurable,
    (hY.map L).map_eq_gaussianReal]
  have hv' : (Var[L ∘ Y; μ]).toNNReal ≠ 0 :=
    (Real.toNNReal_pos.mpr hv).ne'
  exact (gaussianReal_absolutelyContinuous _ hv') (measure_singleton x)

end CubeBrownian
#print axioms CubeBrownian.gaussian_measure_null_hyperplane
