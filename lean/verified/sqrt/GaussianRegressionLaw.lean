import GaussianResidual
import GaussianWeakFaces

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology ProbabilityTheory RealInnerProductSpace
namespace CubeBrownian

theorem gaussian_regression_shift_hasGaussianLaw
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (μ : Measure Ω) (Z : Ω → ℝ) (D : Ω → E) (c : E)
    (hZD : HasGaussianLaw (fun w ↦ (Z w,D w)) μ) (x : ℝ) :
    HasGaussianLaw (fun w ↦ D w - Z w • c + x • c) μ := by
  let B : (ℝ × E) →L[ℝ] E := ContinuousLinearMap.snd ℝ ℝ E -
    (ContinuousLinearMap.fst ℝ ℝ E).smulRight c
  let R : Ω → E := fun w ↦ D w-Z w • c
  let T : E → E := fun z ↦ z+x • c
  have hR : HasGaussianLaw R μ := hZD.map_fun B
  have hT : Measurable T := by dsimp [T]; fun_prop
  refine ⟨hT.aemeasurable.comp_aemeasurable hR.aemeasurable,?_⟩
  change IsGaussian (μ.map (T ∘ R))
  rw [← AEMeasurable.map_map_of_aemeasurable hT.aemeasurable hR.aemeasurable]
  let _ := hR.isGaussian_map
  dsimp only [T]
  infer_instance

/-- Convert a sequence of conditional regression face laws into real convergence
of face masses, without a positive-definite assumption on the residual. -/
theorem gaussian_regression_face_limit
    {Ω E J : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (μ : ℕ → Measure Ω) (ν : Measure Ω) [∀ n, IsProbabilityMeasure (μ n)] [IsProbabilityMeasure ν]
    (Z : ℕ → Ω → ℝ) (D : ℕ → Ω → E) (c : ℕ → E)
    (hZD : ∀ n, HasGaussianLaw (fun w ↦ (Z n w,D n w)) (μ n)) (x : ℝ)
    (Y : Ω → E) (hY : HasGaussianLaw Y ν)
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
  have H := gaussian_tendstoInDistribution_of_moments μ ν X Y hX hY hm hv
  exact gaussian_finite_faces_tendsto_of_weak H.tendsto J₀ l a strict hl hNull

end CubeBrownian
#print axioms CubeBrownian.gaussian_regression_face_limit
