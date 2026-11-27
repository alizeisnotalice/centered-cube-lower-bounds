import GaussianResidual

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory
namespace CubeBrownian

/-- Exact scalar regression moments. Only the center-variance enters; singular
difference covariance needs no special handling. -/
theorem gaussian_regression_projected_moments
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (μ : Measure Ω) (Z : Ω → ℝ) (D : Ω → E) (c : E)
    (hZD : HasGaussianLaw (fun w ↦ (Z w,D w)) μ)
    (L : StrongDual ℝ E) (hCov : cov[Z,L ∘ D;μ] = L c * Var[Z; μ])
    (x : ℝ) :
    let Y := fun w ↦ L (D w - Z w • c + x • c)
    (∫ w, Y w ∂μ) = (∫ w, L (D w) ∂μ) +
      (L c)*(x-(∫ w, Z w ∂μ)) ∧
    Var[Y; μ] = Var[L ∘ D; μ] - (L c)^2 * Var[Z; μ] := by
  dsimp only
  let _ := hZD.isProbabilityMeasure
  let M : Ω → ℝ := L ∘ D
  let b := L c
  have hZ := hZD.fst.memLp_two
  have hM : MemLp M 2 μ := (hZD.snd.map L).memLp_two
  have hy : (fun w ↦ L (D w - Z w • c + x • c)) =
      fun w ↦ M w - b*Z w + x*b := by
    funext w
    simp [M,b,mul_comm]
  rw [hy]
  have hV : MemLp (fun w ↦ b*Z w) 2 μ := hZ.const_mul b
  have hS : Integrable (fun w ↦ M w - b*Z w) μ := (hM.sub hV).integrable one_le_two
  constructor
  · rw [integral_add hS (integrable_const _),
      integral_sub (hM.integrable one_le_two) (hV.integrable one_le_two),
      integral_const_mul,integral_const]
    simp only [probReal_univ,smul_eq_mul,one_mul]
    change (∫ w, M w ∂μ) - b * (∫ w, Z w ∂μ) + x*b =
      (∫ w, M w ∂μ)+b*(x-(∫ w, Z w ∂μ))
    ring
  · rw [variance_add_const hS.aestronglyMeasurable,
      variance_fun_sub hM hV,variance_const_mul,
      covariance_const_mul_right,covariance_comm M Z]
    change cov[Z,M;μ] = b * Var[Z; μ] at hCov
    rw [hCov]
    change Var[M; μ] - 2*(b*(b*Var[Z;μ])) + b^2*Var[Z;μ] =
      Var[M;μ] - b^2*Var[Z;μ]
    ring

end CubeBrownian
#print axioms CubeBrownian.gaussian_regression_projected_moments
