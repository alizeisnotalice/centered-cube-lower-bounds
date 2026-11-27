import IsonormalWinnerLimitLaw
import Mathlib.Analysis.InnerProductSpace.PiL2

open MeasureTheory ProbabilityTheory Set Filter WithLp
open scoped NNReal ENNReal Topology ProbabilityTheory RealInnerProductSpace
namespace CubeBrownian

noncomputable def isoEuclidScores
    {Ω H I : Type*} [Fintype I] [SeminormedAddCommGroup H] [NormedSpace ℝ H]
    (W : H →ₗ[ℝ] (Ω → ℝ)) (k : ℝ≥0) (f : I → H) (w : Ω) : EuclideanSpace ℝ I :=
  toLp 2 (fun i ↦ isoScore W k (f i) w)

theorem isoEuclidScores_hasGaussianLaw
    {Ω H I : Type*} [Fintype I] [MeasurableSpace Ω] [SeminormedAddCommGroup H] [NormedSpace ℝ H]
    (μ : Measure Ω) (W : H →ₗ[ℝ] (Ω → ℝ))
    (hW : ∀ x, HasLaw (W x) (gaussianReal 0 (isoVar 1 x)) μ)
    (k : ℝ≥0) (f : I → H) :
    HasGaussianLaw (isoEuclidScores W k f) μ :=
  (isoScore_finite_hasGaussianLaw μ W hW k f).map_equiv_fun
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : I ↦ ℝ)).symm

/-- The only limiting boundary condition needed by the winner comparison is
nonzero scalar variance at each distinct relative node. -/
theorem isoEuclidScores_winner_null_face
    {Ω H I : Type*} [Fintype I] [MeasurableSpace Ω] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (W : H →ₗ[ℝ] (Ω → ℝ))
    (hW : ∀ x, HasLaw (W x) (gaussianReal 0 (isoVar 1 x)) μ)
    {k : ℝ≥0} (hk : 0 < k) (f : I → H) (i j : I) (hij : f i ≠ f j) :
    (μ.map (isoEuclidScores W k (fun i ↦ f i-f j)))
      ((EuclideanSpace.proj (𝕜:=ℝ) i) ⁻¹' {(0:ℝ)}) = 0 := by
  apply gaussian_measure_null_hyperplane μ _ (isoEuclidScores_hasGaussianLaw μ W hW k _)
  change 0 < Var[isoScore W k (f i-f j); μ]
  rw [← covariance_self (isoScore_hasLaw μ W hW k (f i-f j)).aemeasurable,
    isoScore_covariance μ W hW,real_inner_self_eq_norm_sq]
  exact mul_pos (by exact_mod_cast hk) (sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hij)))

end CubeBrownian
#print axioms CubeBrownian.isoEuclidScores_winner_null_face
