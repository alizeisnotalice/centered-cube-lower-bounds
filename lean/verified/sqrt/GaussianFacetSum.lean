import ActualIidFaceBound
import Mathlib.Probability.Distributions.Gaussian.Basic

open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators ProbabilityTheory
namespace CubeSqrtProbability

instance gaussian_centered_facet {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Matrix ι ι ℝ) : IsGaussian (centeredGaussianCompanion S) := by
  let L : EuclideanSpace ℝ ι →L[ℝ] (ι → ℝ) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι ↦ ℝ)).toContinuousLinearMap
  change IsGaussian ((multivariateGaussian 0 S).map L)
  infer_instance

instance gaussian_sumLaw {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (ν : Measure E) [IsGaussian ν] (n : ℕ) : IsGaussian (sumLaw ν n) := by
  induction n with
  | zero =>
    change IsGaussian (Measure.dirac (0:E))
    infer_instance
  | succ n ih =>
    change IsGaussian (sumLaw ν n ∗ ν)
    infer_instance

/-- Every linear projection of the summed Gaussian companion has the exact
one-coordinate Gaussian mean and variance multiplied by the iid count. -/
theorem gaussian_sumLaw_linear_marginal
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [MeasurableAdd₂ E]
    (ν : Measure E) [IsGaussian ν] (n : ℕ) (L : E →L[ℝ] ℝ) :
    (sumLaw ν n).map L =
      gaussianReal ((n:ℝ)*(∫ x, L x ∂ν)) (n • (variance L ν).toNNReal) := by
  induction n with
  | zero =>
    simp [sumLaw,Measure.map_dirac' L.continuous.measurable,gaussianReal_zero_var]
  | succ n ih =>
    change (sumLaw ν n ∗ ν).map L = _
    rw [Measure.map_conv_continuousLinearMap,ih,IsGaussian.map_eq_gaussianReal,
      gaussianReal_conv_gaussianReal,succ_nsmul]
    congr 1
    push_cast
    ring

end CubeSqrtProbability
#print axioms CubeSqrtProbability.gaussian_centered_facet
#print axioms CubeSqrtProbability.gaussian_sumLaw
#print axioms CubeSqrtProbability.gaussian_sumLaw_linear_marginal
