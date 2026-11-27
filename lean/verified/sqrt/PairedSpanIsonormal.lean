import IsonormalCoupling
import Mathlib.Probability.Distributions.Gaussian.Multivariate

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology ProbabilityTheory RealInnerProductSpace
namespace CubeBrownian

/-- The canonical isonormal realization in a finite-dimensional real Hilbert
space: evaluate the inner product against a standard Gaussian vector. -/
noncomputable def pairedSpanIsonormal (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] :
    H →ₗ[ℝ] (H → ℝ) where
  toFun x w := ⟪x,w⟫
  map_add' x y := funext fun w ↦ inner_add_left x y w
  map_smul' a x := funext fun w ↦ real_inner_smul_left x w a

theorem measurable_pairedSpanIsonormal
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasurableSpace H] [BorelSpace H] (x : H) :
    Measurable (pairedSpanIsonormal H x) := (innerSL ℝ x).continuous.measurable

theorem pairedSpanIsonormal_hasLaw
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
    [MeasurableSpace H] [BorelSpace H] (x : H) :
    HasLaw (pairedSpanIsonormal H x) (gaussianReal 0 (isoVar 1 x)) (stdGaussian H) := by
  refine ⟨(measurable_pairedSpanIsonormal x).aemeasurable,?_⟩
  let L := innerSL ℝ x
  change (stdGaussian H).map L = _
  rw [IsGaussian.map_eq_gaussianReal L,integral_strongDual_stdGaussian,
    variance_dual_stdGaussian,innerSL_apply_norm]
  congr 1
  apply NNReal.eq
  simp [isoVar,Real.toNNReal_of_nonneg (sq_nonneg ‖x‖)]

end CubeBrownian
#print axioms CubeBrownian.pairedSpanIsonormal_hasLaw
