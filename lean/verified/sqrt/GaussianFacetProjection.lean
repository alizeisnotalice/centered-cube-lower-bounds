import GaussianFacetSumMoments
import FaceWeightedTransfer
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic

open MeasureTheory ProbabilityTheory WithLp
open scoped NNReal ProbabilityTheory
namespace CubeSqrtProbability

noncomputable def winnerFacetProjection {k : ℕ} (j : Fin k) :
    (WinnerFacet j → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin k) := by
  classical
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin k ↦ ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i ↦ if hi : i ≠ j then
      ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : WinnerFacet j ↦ ℝ) (.inr ⟨i,hi⟩) else 0)

theorem winnerFacetProjection_apply {k : ℕ} (j : Fin k) (x : WinnerFacet j → ℝ) :
    winnerFacetProjection j x = toLp 2 (facetRelative j x) := by
  ext i
  by_cases hi : i ≠ j
  · simp [winnerFacetProjection,facetRelative,hi]
  · simp [winnerFacetProjection,facetRelative,not_ne_iff.mp hi]

noncomputable def winnerFacetJoint {k : ℕ} (j : Fin k) :
    (WinnerFacet j → ℝ) →L[ℝ] ℝ × EuclideanSpace ℝ (Fin k) :=
  (ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : WinnerFacet j ↦ ℝ) (.inl true)).prod
    (winnerFacetProjection j)

/-- The nuisance base and all relative coordinates share an actual joint
Gaussian law after applying the projection to the finite-face companion. -/
theorem winnerFacet_shifted_sum_hasGaussianLaw {k : ℕ} (j : Fin k)
    (S : Matrix (WinnerFacet j) (WinnerFacet j) ℝ) (n : ℕ)
    (z : WinnerFacet j → ℝ) (h : ℝ) :
    HasGaussianLaw (fun x ↦ ((z+x) (.inl true)-h,
      toLp 2 (facetRelative j (z+x))))
      (sumLaw (centeredGaussianCompanion S) n) := by
  classical
  let ν := sumLaw (centeredGaussianCompanion S) n
  let L := winnerFacetJoint j
  let c := L z-((h:ℝ),(0 : EuclideanSpace ℝ (Fin k)))
  have he : (fun x ↦ ((z+x) (.inl true)-h,toLp 2 (facetRelative j (z+x)))) =
      (fun y ↦ c+y) ∘ L := by
    funext x
    simp only [Function.comp_apply,c,← map_add,sub_add_eq_add_sub]
    rw [← winnerFacetProjection_apply]
    change (_,_) = (_,winnerFacetProjection j (z+x)-0)
    simp [L,winnerFacetJoint]
  rw [he]
  refine ⟨by fun_prop,?_⟩
  change IsGaussian (ν.map ((fun y ↦ c+y) ∘ L))
  rw [← Measure.map_map (by fun_prop) L.continuous.measurable]
  infer_instance

end CubeSqrtProbability
#print axioms CubeSqrtProbability.winnerFacetProjection_apply
#print axioms CubeSqrtProbability.winnerFacet_shifted_sum_hasGaussianLaw
