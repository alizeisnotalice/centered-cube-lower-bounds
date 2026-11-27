import GaussianRegressionLawTwoSpaces
import GaussianWinnerProjectedLimit
import GaussianWinnerThinLimit
import GaussianRegressionLaw
import GaussianResidualMoments

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology ProbabilityTheory RealInnerProductSpace
namespace CubeBrownian

theorem gaussian_winner_projected_thinLayer_tendsto_twoSpaces
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
    (hm : ∀ x ∈ Ioi (0:ℝ), ∀ L : E,
      Tendsto (fun n ↦ ∫ w, ⟪L,D n w-Z n w • c n+x • c n⟫ ∂(μ n)) atTop
        (𝓝 (∫ w, ⟪L,Y w⟫ ∂ν)))
    (hVar : ∀ x ∈ Ioi (0:ℝ), ∀ L : E,
      Tendsto (fun n ↦ Var[fun w ↦ ⟪L,D n w-Z n w • c n+x • c n⟫; μ n]) atTop
        (𝓝 (Var[fun w ↦ ⟪L,Y w⟫; ν])))
    (J₀ : Finset J) (l : J → E → ℝ) (b : J → ℝ) (strict : J → Bool)
    (hl : ∀ j ∈ J₀, Continuous (l j))
    (hNull : ∀ j ∈ J₀, (ν.map Y) (l j ⁻¹' {b j}) = 0) :
    let F : Set E := {z | ∀ j ∈ J₀, z ∈ l j ⁻¹' (if strict j then Iio (b j) else Iic (b j))}
    Tendsto (fun n ↦ u n *
      (∫⁻ w in {w | 0 < Z n w ∧ D n w ∈ F}, ENNReal.ofReal (Real.exp (-(Z n w))) ∂(μ n)).toReal)
      atTop (𝓝 (φ 0 * ((ν.map Y) F).toReal)) := by
  dsimp only
  let A (j : J) := if strict j then Iio (b j) else Iic (b j)
  let F : Set E := {z | ∀ j ∈ J₀, z ∈ l j ⁻¹' A j}
  have hF : MeasurableSet F := by
    have hJ : F = ⋂ j : J₀, l j.1 ⁻¹' A j.1 := by ext z; simp [F]
    rw [hJ]
    apply MeasurableSet.iInter
    intro j
    apply (hl j.1 j.2).measurable
    unfold A
    split <;> first | exact measurableSet_Iio | exact measurableSet_Iic
  let _ : IsProbabilityMeasure (ν.map Y) :=
    (Measure.isProbabilityMeasure_map_iff hY.aemeasurable).2 inferInstance
  refine gaussian_winner_thinLayer_tendsto μ Z D c hmZ hmD hZD hc a u v hv hZ hu hScale hOffset
    F hF (measure_ne_top _ _) ?_
  intro x hx
  have H := gaussian_regression_face_limit_twoSpaces μ ν Z D c hZD x Y hY (hm x hx) (hVar x hx)
    J₀ l b strict hl hNull
  apply H.congr
  intro n
  have hYₙ : Measurable (fun w ↦ D n w-Z n w • c n+x • c n) :=
    ((hmD n).sub ((hmZ n).smul measurable_const)).add_const _
  exact Measure.map_apply hYₙ hF

end CubeBrownian
#print axioms CubeBrownian.gaussian_winner_projected_thinLayer_tendsto_twoSpaces
