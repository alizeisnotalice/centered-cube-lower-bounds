import GaussianCovarianceMatch
import Mathlib.Probability.BrownianMotion.GaussianProjectiveFamily

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace CubeSqrtProbability

noncomputable def centeredGaussianCompanion {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Matrix ι ι ℝ) : Measure (ι → ℝ) :=
  (multivariateGaussian 0 S).map (MeasurableEquiv.toLp 2 (ι → ℝ)).symm

instance centeredGaussianCompanion_probability {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Matrix ι ι ℝ) : IsProbabilityMeasure (centeredGaussianCompanion S) := by
  unfold centeredGaussianCompanion
  infer_instance

theorem centeredGaussianCompanion_marginal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Matrix ι ι ℝ) (hS : S.PosSemidef) (i : ι) :
    (centeredGaussianCompanion S).map (fun x ↦ x i) = gaussianReal 0 (S i i).toNNReal := by
  unfold centeredGaussianCompanion
  rw [Measure.map_map (measurable_pi_apply i) (MeasurableEquiv.measurable _)]
  exact (measurePreserving_eval_multivariateGaussian (μ := 0) (i := i) hS).map_eq

theorem centeredGaussianCompanion_mean {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Matrix ι ι ℝ) (hS : S.PosSemidef) (i : ι) :
    (∫ x, x i ∂(centeredGaussianCompanion S)) = 0 := by
  let ν := centeredGaussianCompanion S
  have he := integral_map (μ := ν) (φ := fun d : ι → ℝ ↦ d i)
    (measurable_pi_apply i).aemeasurable (f := fun x : ℝ ↦ x)
    continuous_id.aestronglyMeasurable
  change (∫ x, x ∂(ν.map (fun d ↦ d i))) = ∫ d, d i ∂ν at he
  rw [← he, centeredGaussianCompanion_marginal S hS,
    integral_id_gaussianReal]

theorem centeredGaussianCompanion_second_moment {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Matrix ι ι ℝ) (hS : S.PosSemidef) (i j : ι) :
    (∫ x, x i * x j ∂(centeredGaussianCompanion S)) = S i j := by
  let g := multivariateGaussian (0 : EuclideanSpace ℝ ι) S
  let e := (MeasurableEquiv.toLp 2 (ι → ℝ)).symm
  change (∫ x, x i * x j ∂(g.map e)) = _
  rw [integral_map e.measurable.aemeasurable (f := fun x : ι → ℝ ↦ x i*x j) (by fun_prop)]
  change (∫ x : EuclideanSpace ℝ ι, x i * x j ∂g) = _
  have hm (k : ι) : (∫ x : EuclideanSpace ℝ ι, x k ∂g) = 0 := by
    have h := (measurePreserving_eval_multivariateGaussian (μ := 0) (i := k) hS).map_eq
    have he := integral_map (μ := g) (φ := fun x : EuclideanSpace ℝ ι ↦ x k)
       (by fun_prop) (f := fun x : ℝ ↦ x) continuous_id.aestronglyMeasurable
    change (∫ x : ℝ, x ∂(g.map (fun x : EuclideanSpace ℝ ι ↦ x k))) =
      ∫ x : EuclideanSpace ℝ ι, x k ∂g at he
    rw [← he,h,integral_id_gaussianReal]
    rfl
  have hc := covariance_eval_multivariateGaussian (μ := (0 : EuclideanSpace ℝ ι)) hS i j
  change covariance (fun x : EuclideanSpace ℝ ι ↦ x i) (fun x ↦ x j) g = _ at hc
  unfold covariance at hc
  simpa only [hm i,hm j,sub_zero] using hc

end CubeSqrtProbability
#print axioms CubeSqrtProbability.centeredGaussianCompanion_second_moment
