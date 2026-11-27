import GaussianWeakFacesTwoSpaces
import GaussianRegressionLaw
import GaussianResidual
import GaussianWeakFaces

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology ProbabilityTheory RealInnerProductSpace
namespace CubeBrownian

theorem gaussian_regression_face_limit_twoSpaces
    {Ω Ω' E J : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (μ : ℕ → Measure Ω) (ν : Measure Ω') [∀ n, IsProbabilityMeasure (μ n)] [IsProbabilityMeasure ν]
    (Z : ℕ → Ω → ℝ) (D : ℕ → Ω → E) (c : ℕ → E)
    (hZD : ∀ n, HasGaussianLaw (fun w ↦ (Z n w,D n w)) (μ n)) (x : ℝ)
    (Y : Ω' → E) (hY : HasGaussianLaw Y ν)
    (hm : ∀ v : E, Tendsto (fun n ↦ ∫ w, ⟪v,D n w-Z n w • c n+x • c n⟫ ∂(μ n)) atTop
      (𝓝 (∫ w, ⟪v,Y w⟫ ∂ν)))
    (hv : ∀ v : E, Tendsto (fun n ↦ Var[fun w ↦ ⟪v,D n w-Z n w • c n+x • c n⟫; μ n]) atTop
      (𝓝 (Var[fun w ↦ ⟪v,Y w⟫; ν])))
    (J₀ : Finset J) (l : J → E → ℝ) (a : J → ℝ) (strict : J → Bool)
    (hl : ∀ j ∈ J₀, Continuous (l j))
    (hNull : ∀ j ∈ J₀, (ν.map Y) (l j ⁻¹' {a j}) = 0) :
    let F : Set E := {z | ∀ j ∈ J₀, z ∈ l j ⁻¹' (if strict j then Iio (a j) else Iic (a j))}
    Tendsto (fun n ↦ ((μ n).map (fun w ↦ D n w-Z n w • c n+x • c n)) F)
       atTop (𝓝 ((ν.map Y) F)) := by
  dsimp only
  let X (n : ℕ) (w : Ω) := D n w-Z n w • c n+x • c n
  have hX (n) : HasGaussianLaw (X n) (μ n) :=
    gaussian_regression_shift_hasGaussianLaw (μ n) (Z n) (D n) (c n) (hZD n) x
  have H := gaussian_tendstoInDistribution_of_moments_twoSpaces μ ν X Y hX hY hm hv
  exact gaussian_finite_faces_tendsto_of_weak H.tendsto J₀ l a strict hl hNull

end CubeBrownian
#print axioms CubeBrownian.gaussian_regression_face_limit_twoSpaces
