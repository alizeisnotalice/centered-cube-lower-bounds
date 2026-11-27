import GaussianWeakFaces
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Topology.Order.OrderClosed

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ProbabilityTheory RealInnerProductSpace

namespace CubeBrownian

theorem gaussian_tendstoInDistribution_of_moments_twoSpaces
    {Ω Ω' E : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (μ : ℕ → Measure Ω) (ν : Measure Ω')
    [∀ n, IsProbabilityMeasure (μ n)] [IsProbabilityMeasure ν]
    (X : ℕ → Ω → E) (Y : Ω' → E)
    (hX : ∀ n, HasGaussianLaw (X n) (μ n)) (hY : HasGaussianLaw Y ν)
    (hm : ∀ v : E, Tendsto (fun n ↦ ∫ ω, ⟪v, X n ω⟫ ∂(μ n)) atTop
      (𝓝 (∫ ω, ⟪v, Y ω⟫ ∂ν)))
    (hv : ∀ v : E, Tendsto (fun n ↦ Var[fun ω ↦ ⟪v, X n ω⟫; μ n]) atTop
      (𝓝 (Var[fun ω ↦ ⟪v, Y ω⟫; ν]))) :
    TendstoInDistribution X atTop Y μ ν := by
  apply TendstoInDistribution.of_tendsto_charFun (fun n ↦ (hX n).aemeasurable) hY.aemeasurable
  intro v
  simp_rw [fun n ↦ (hX n).charFun_map_eq v, hY.charFun_map_eq v]
  have hm' := Complex.continuous_ofReal.continuousAt.tendsto.comp (hm v)
  have hv' := Complex.continuous_ofReal.continuousAt.tendsto.comp (hv v)
  exact Complex.continuous_exp.continuousAt.tendsto.comp
    ((hm'.mul_const Complex.I).sub (hv'.div_const 2))

end CubeBrownian
#print axioms CubeBrownian.gaussian_tendstoInDistribution_of_moments_twoSpaces
