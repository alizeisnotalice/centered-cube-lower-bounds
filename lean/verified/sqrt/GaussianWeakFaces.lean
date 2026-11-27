import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Topology.Order.OrderClosed

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ProbabilityTheory RealInnerProductSpace

namespace CubeBrownian

/-- No determinant or inverse covariance is used: projected first and second
moments suffice for convergence of arbitrary, possibly singular, Gaussian laws. -/
theorem gaussian_tendstoInDistribution_of_moments
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (μ : ℕ → Measure Ω) (ν : Measure Ω)
    [∀ n, IsProbabilityMeasure (μ n)] [IsProbabilityMeasure ν]
    (X : ℕ → Ω → E) (Y : Ω → E)
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

/-- Measures of any fixed finite intersection of open or closed half-spaces
converge provided each limiting boundary hyperplane is null. -/
theorem gaussian_finite_faces_tendsto_of_weak
    {E J : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    {μ : ProbabilityMeasure E} {μs : ℕ → ProbabilityMeasure E}
    (hT : Tendsto μs atTop (𝓝 μ)) (J₀ : Finset J)
    (l : J → E → ℝ) (a : J → ℝ) (strict : J → Bool)
    (hc : ∀ j ∈ J₀, Continuous (l j))
    (hNull : ∀ j ∈ J₀, (μ : Measure E) (l j ⁻¹' {a j}) = 0) :
    Tendsto (fun n ↦ (μs n : Measure E) {z | ∀ j ∈ J₀,
      z ∈ l j ⁻¹' (if strict j then Iio (a j) else Iic (a j))})
      atTop (𝓝 ((μ : Measure E) {z | ∀ j ∈ J₀,
        z ∈ l j ⁻¹' (if strict j then Iio (a j) else Iic (a j))})) := by
  classical
  let F (j : J) : Set E := l j ⁻¹' (if strict j then Iio (a j) else Iic (a j))
  have hF (j) (hj : j ∈ J₀) : (μ : Measure E) (frontier (F j)) = 0 := by
    apply measure_mono_null _ (hNull j hj)
    apply Set.Subset.trans ((hc j hj).frontier_preimage_subset _)
    apply preimage_mono
    cases hj' : strict j <;> simp [hj', frontier_Iic, frontier_Iio]
  have hFin (K : Finset J) (hK : K ⊆ J₀) :
      (μ : Measure E) (frontier {z | ∀ j ∈ K, z ∈ F j}) = 0 := by
    induction K using Finset.induction_on with
    | empty =>
      simp
    | @insert j K hj ih =>
      have hEq : {z | ∀ j' ∈ (insert j K : Finset J), z ∈ F j'} =
          F j ∩ {z | ∀ j' ∈ K, z ∈ F j'} := by
        ext z
        simp
      rw [hEq]
      apply measure_mono_null (frontier_inter_subset _ _)
      exact measure_union_null (measure_mono_null inter_subset_left (hF j (hK (Finset.mem_insert_self ..))))
        (measure_mono_null inter_subset_right (ih (fun k hk ↦ hK (Finset.mem_insert_of_mem hk))))
  exact ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hT
    (hFin J₀ Subset.rfl)

end CubeBrownian
#print axioms CubeBrownian.gaussian_tendstoInDistribution_of_moments
#print axioms CubeBrownian.gaussian_finite_faces_tendsto_of_weak
