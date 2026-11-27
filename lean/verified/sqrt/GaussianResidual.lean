import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

namespace CubeBrownian

/-- Gaussian regression without any nonsingularity assumption for the residual. -/
theorem gaussian_residual_indep
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (μ : Measure Ω) (Z : Ω → ℝ) (D : Ω → E) (c : E)
    (hZD : HasGaussianLaw (fun w ↦ (Z w, D w)) μ)
    (hc : ∀ L : StrongDual ℝ E, cov[Z, L ∘ D; μ] = L c * Var[Z; μ]) :
    IndepFun Z (fun w ↦ D w - Z w • c) μ := by
  let _ := hZD.isProbabilityMeasure
  let A : (ℝ × E) →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ E
  let B : (ℝ × E) →L[ℝ] E :=
    ContinuousLinearMap.snd ℝ ℝ E - A.smulRight c
  have hZR : HasGaussianLaw (fun w ↦ (Z w, D w - Z w • c)) μ := hZD.map (A.prod B)
  apply hZR.indepFun_of_covariance_strongDual
  intro L₁ L₂
  have hL₁ : L₁ ∘ Z = fun w ↦ L₁ 1 * Z w := by
    funext w
    change L₁ (Z w) = _
    calc
      L₁ (Z w) = L₁ (Z w • (1 : ℝ)) := by simp
      _ = L₁ 1 * Z w := by rw [map_smul]; exact mul_comm _ _
  have hL₂ : L₂ ∘ (fun w ↦ D w - Z w • c) =
      fun w ↦ (L₂ ∘ D) w - L₂ c * Z w := by
    funext w
    change L₂ (D w - Z w • c) = _
    rw [map_sub, map_smul]
    simp only [Function.comp_apply, smul_eq_mul]
    rw [mul_comm (Z w)]
  have hZm := hZD.fst.memLp_two
  rw [hL₁, hL₂, covariance_const_mul_left,
    covariance_fun_sub_right hZm (hZD.snd.map L₂).memLp_two (hZm.const_mul _),
    covariance_const_mul_right, covariance_self hZD.fst.aemeasurable, hc, sub_self, mul_zero]

end CubeBrownian
#print axioms CubeBrownian.gaussian_residual_indep
