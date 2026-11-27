import GaussianWinnerProjectedLimitTwoSpaces
import GaussianWinnerRawLimit
import GaussianWinnerProjectedLimit
import GaussianRegressionAsymptotic

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology ProbabilityTheory RealInnerProductSpace
namespace CubeBrownian

theorem gaussian_winner_raw_thinLayer_tendsto_twoSpaces
    {Ω Ω' E J : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (μ : ℕ → Measure Ω) (ν : Measure Ω')
    [∀ n, IsProbabilityMeasure (μ n)] [IsProbabilityMeasure ν]
    (Z : ℕ → Ω → ℝ) (D : ℕ → Ω → E) (c : ℕ → E)
    (hmZ : ∀ n, Measurable (Z n)) (hmD : ∀ n, Measurable (D n))
    (hZD : ∀ n, HasGaussianLaw (fun w ↦ (Z n w,D n w)) (μ n))
    (hc : ∀ n (L : StrongDual ℝ E), cov[Z n, L ∘ D n; μ n] = L (c n) * Var[Z n; μ n])
    (a u : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (hv : ∀ n, 0 < v n) (hZ : ∀ n, HasLaw (Z n) (gaussianReal (a n) (v n)) (μ n))
    (hu : ∀ n, 0 ≤ u n)
    (hScale : Tendsto (fun n ↦ u n / Real.sqrt (v n:ℝ)) atTop (𝓝 1))
    (hOffset : ∀ x ∈ Ioi (0:ℝ), Tendsto (fun n ↦ (x-a n)/Real.sqrt (v n:ℝ)) atTop (𝓝 0))
    (Y : Ω' → E) (hY : HasGaussianLaw Y ν)
    (hBaseVar : Tendsto (fun n ↦ Var[Z n; μ n]) atTop atTop)
    (A : ℝ) (hBaseMean : ∀ᶠ n in atTop, |∫ w, Z n w ∂(μ n)| ≤ A)
    (hBaseCov : ∀ L : StrongDual ℝ E, ∃ R : ℝ, ∀ᶠ n in atTop, |cov[Z n,L ∘ D n; μ n]| ≤ R)
    (hm : ∀ L : E, Tendsto (fun n ↦ ∫ w, ⟪L,D n w⟫ ∂(μ n)) atTop
        (𝓝 (∫ w, ⟪L,Y w⟫ ∂ν)))
    (hVar : ∀ L : E, Tendsto (fun n ↦ Var[fun w ↦ ⟪L,D n w⟫; μ n]) atTop
        (𝓝 (Var[fun w ↦ ⟪L,Y w⟫; ν])))
    (J₀ : Finset J) (l : J → E → ℝ) (b : J → ℝ) (strict : J → Bool)
    (hl : ∀ j ∈ J₀, Continuous (l j))
    (hNull : ∀ j ∈ J₀, (ν.map Y) (l j ⁻¹' {b j}) = 0) :
    let F : Set E := {z | ∀ j ∈ J₀, z ∈ l j ⁻¹' (if strict j then Iio (b j) else Iic (b j))}
    Tendsto (fun n ↦ u n *
      (∫⁻ w in {w | 0 < Z n w ∧ D n w ∈ F}, ENNReal.ofReal (Real.exp (-(Z n w))) ∂(μ n)).toReal)
      atTop (𝓝 (φ 0 * ((ν.map Y) F).toReal)) := by
  have H (x : ℝ) (z : E) :
      Tendsto (fun n ↦ ∫ w, ⟪z,D n w-Z n w • c n+x • c n⟫ ∂(μ n)) atTop
        (𝓝 (∫ w, ⟪z,Y w⟫ ∂ν)) ∧
      Tendsto (fun n ↦ Var[fun w ↦ ⟪z,D n w-Z n w • c n+x • c n⟫; μ n]) atTop
        (𝓝 (Var[fun w ↦ ⟪z,Y w⟫; ν])) := by
    let L := innerSL ℝ z
    obtain ⟨R,hR⟩ := hBaseCov L
    have key := gaussian_regression_projected_moment_limits μ Z D c hZD L (fun n ↦ hc n L)
      x A R (∫ w, ⟪z,Y w⟫ ∂ν) (Var[fun w ↦ ⟪z,Y w⟫; ν])
      hBaseVar hBaseMean hR (hm z) (hVar z)
    exact key
  exact gaussian_winner_projected_thinLayer_tendsto_twoSpaces μ ν Z D c hmZ hmD hZD hc a u v hv hZ hu
    hScale hOffset Y hY (fun x _ z ↦ (H x z).1) (fun x _ z ↦ (H x z).2)
    J₀ l b strict hl hNull

end CubeBrownian
#print axioms CubeBrownian.gaussian_winner_raw_thinLayer_tendsto_twoSpaces
