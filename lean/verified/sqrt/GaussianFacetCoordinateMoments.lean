import GaussianFacetSumMoments

open MeasureTheory ProbabilityTheory
open scoped NNReal ProbabilityTheory
namespace CubeSqrtProbability

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (S : Matrix ι ι ℝ) (hS : S.PosSemidef) (n : ℕ)
include hS

theorem gaussian_companion_affine_coord_mean (i : ι) (c : ℝ) :
    (∫ x, c+x i ∂sumLaw (centeredGaussianCompanion S) n) = c := by
  let ν := centeredGaussianCompanion S
  let R := sumLaw ν n
  let L : (ι → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj i
  have hi : Integrable (fun x : ι → ℝ ↦ x i) R :=
    IsGaussian.integrable_dual R L
  rw [integral_add (integrable_const _) hi,integral_const]
  simp only [probReal_univ,one_smul]
  have hM := gaussian_sumLaw_linear_mean ν n L
  change (∫ x : ι → ℝ, x i ∂R) = (n:ℝ)*∫ x : ι → ℝ, x i ∂ν at hM
  rw [hM,centeredGaussianCompanion_mean S hS,mul_zero,add_zero]

theorem gaussian_companion_affine_coord_cov (i j : ι) (a b : ℝ) :
    covariance (fun x ↦ a+x i) (fun x ↦ b+x j)
      (sumLaw (centeredGaussianCompanion S) n) = (n:ℝ)*S i j := by
  let ν := centeredGaussianCompanion S
  let R := sumLaw ν n
  let L (a : ι) : (ι → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj a
  have hI (a : ι) : Integrable (fun x : ι → ℝ ↦ x a) R :=
    IsGaussian.integrable_dual R (L a)
  rw [covariance_const_add_left (hI i),covariance_const_add_right (hI j)]
  have h := gaussian_sumLaw_linear_covariance ν n (L i) (L j)
  change covariance (fun x : ι → ℝ ↦ x i) (fun x ↦ x j) R =
    (n:ℝ)*covariance (fun x : ι → ℝ ↦ x i) (fun x ↦ x j) ν at h
  rw [h]
  congr 1
  unfold covariance
  rw [centeredGaussianCompanion_mean S hS,centeredGaussianCompanion_mean S hS]
  simp only [sub_zero]
  exact centeredGaussianCompanion_second_moment S hS i j

theorem gaussian_companion_affine_coord_law (i : ι) (c : ℝ) :
    HasLaw (fun x ↦ c+x i) (gaussianReal c (n • (S i i).toNNReal))
      (sumLaw (centeredGaussianCompanion S) n) := by
  refine ⟨(measurable_const.add (measurable_pi_apply i)).aemeasurable,?_⟩
  have he : (fun x : ι → ℝ ↦ c+x i) = (fun t : ℝ ↦ c+t) ∘ fun x ↦ x i := rfl
  rw [he,← Measure.map_map (by fun_prop) (by fun_prop),
    sumLaw_centeredGaussian_marginal S hS,gaussianReal_map_const_add,zero_add]

end
end CubeSqrtProbability
#print axioms CubeSqrtProbability.gaussian_companion_affine_coord_mean
#print axioms CubeSqrtProbability.gaussian_companion_affine_coord_cov
#print axioms CubeSqrtProbability.gaussian_companion_affine_coord_law
