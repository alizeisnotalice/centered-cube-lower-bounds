import GaussianFacetSum

open MeasureTheory ProbabilityTheory
open scoped NNReal ProbabilityTheory
namespace CubeSqrtProbability

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (ν : Measure E) [IsGaussian ν] (n : ℕ)

theorem gaussian_sumLaw_linear_mean (L : E →L[ℝ] ℝ) :
    (∫ x, L x ∂sumLaw ν n) = (n:ℝ)*∫ x, L x ∂ν := by
  calc
    _ = ∫ x : ℝ, x ∂((sumLaw ν n).map L) := (integral_map
      (μ:=sumLaw ν n) (φ := L) L.continuous.measurable.aemeasurable
      (f:=id) continuous_id.aestronglyMeasurable).symm
    _ = _ := by rw [gaussian_sumLaw_linear_marginal,integral_id_gaussianReal]

theorem gaussian_sumLaw_linear_variance (L : E →L[ℝ] ℝ) :
    variance L (sumLaw ν n) = (n:ℝ)*variance L ν := by
  rw [← variance_id_map L.continuous.measurable.aemeasurable,gaussian_sumLaw_linear_marginal,
    variance_id_gaussianReal]
  simp [nsmul_eq_mul,Real.toNNReal_of_nonneg,variance_nonneg]

theorem gaussian_sumLaw_linear_covariance (L M : E →L[ℝ] ℝ) :
    covariance L M (sumLaw ν n) = (n:ℝ)*covariance L M ν := by
  have hLp (μ : Measure E) [IsGaussian μ] (L : E →L[ℝ] ℝ) : MemLp L 2 μ :=
    IsGaussian.memLp_dual μ L 2 (by norm_num)
  have hV (μ : Measure E) [IsGaussian μ] :
      variance (L+M : E →L[ℝ] ℝ) μ =
        variance L μ + 2*covariance L M μ + variance M μ :=
    variance_fun_add (hLp μ L) (hLp μ M)
  have hh := gaussian_sumLaw_linear_variance ν n (L+M)
  rw [hV,hV,gaussian_sumLaw_linear_variance,gaussian_sumLaw_linear_variance] at hh
  linarith

end
end CubeSqrtProbability
#print axioms CubeSqrtProbability.gaussian_sumLaw_linear_mean
#print axioms CubeSqrtProbability.gaussian_sumLaw_linear_variance
#print axioms CubeSqrtProbability.gaussian_sumLaw_linear_covariance
