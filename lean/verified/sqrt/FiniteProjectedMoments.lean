import Mathlib.Probability.Moments.Variance
import Mathlib.Topology.Algebra.Monoid

open MeasureTheory ProbabilityTheory Finset Filter
open scoped NNReal ENNReal Topology ProbabilityTheory
namespace CubeBrownian

private lemma finite_projected_mean
    {Θ I : Type*} [MeasurableSpace Θ] [Fintype I] (P : Measure Θ) [IsFiniteMeasure P]
    (a : I → ℝ) (V : I → Θ → ℝ) (hV : ∀ i, MemLp (V i) 2 P) :
    (∫ w, ∑ i, a i*V i w ∂P) = ∑ i, a i*(∫ w, V i w ∂P) := by
  rw [integral_finsetSum _ (fun i _ ↦ ((hV i).integrable one_le_two).const_mul _)]
  simp_rw [integral_const_mul]

private lemma finite_projected_variance
    {Θ I : Type*} [MeasurableSpace Θ] [Fintype I] (P : Measure Θ) [IsFiniteMeasure P]
    (a : I → ℝ) (V : I → Θ → ℝ) (hV : ∀ i, MemLp (V i) 2 P) :
    Var[fun w ↦ ∑ i, a i*V i w; P] = ∑ i, ∑ j, a i*(a j*cov[V i,V j;P]) := by
  have hh := variance_fun_sum (μ:=P) (fun i ↦ (hV i).const_mul (a i))
  simp_rw [covariance_const_mul_left,covariance_const_mul_right] at hh
  exact hh

/-- Entrywise finite mean/covariance limits imply every projected-moment
limit, with no covariance rank requirement. The spaces may differ. -/
theorem finite_coordinate_moments_imply_projected
    {Ω Ω' I : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] [Fintype I]
    (μ : ℕ → Measure Ω) (ν : Measure Ω')
    [∀ n, IsFiniteMeasure (μ n)] [IsFiniteMeasure ν]
    (X : ℕ → I → Ω → ℝ) (Y : I → Ω' → ℝ)
    (hX : ∀ n i, MemLp (X n i) 2 (μ n)) (hY : ∀ i, MemLp (Y i) 2 ν)
    (hMean : ∀ i, Tendsto (fun n ↦ ∫ w, X n i w ∂(μ n)) atTop (𝓝 (∫ w, Y i w ∂ν)))
    (hCov : ∀ i j, Tendsto (fun n ↦ cov[X n i,X n j; μ n]) atTop (𝓝 (cov[Y i,Y j;ν])))
    (a : I → ℝ) :
    Tendsto (fun n ↦ ∫ w, ∑ i, a i*X n i w ∂(μ n)) atTop
      (𝓝 (∫ w, ∑ i, a i*Y i w ∂ν)) ∧
    Tendsto (fun n ↦ Var[fun w ↦ ∑ i, a i*X n i w; μ n]) atTop
      (𝓝 (Var[fun w ↦ ∑ i, a i*Y i w; ν])) := by
  constructor
  · simp_rw [fun n ↦ finite_projected_mean (μ n) a (X n) (hX n),finite_projected_mean ν a Y hY]
    exact tendsto_finsetSum _ (fun i _ ↦ (hMean i).const_mul _)
  · simp_rw [fun n ↦ finite_projected_variance (μ n) a (X n) (hX n),finite_projected_variance ν a Y hY]
    exact tendsto_finsetSum _ (fun i _ ↦ tendsto_finsetSum _
      (fun j _ ↦ ((hCov i j).const_mul _).const_mul _))

end CubeBrownian
#print axioms CubeBrownian.finite_coordinate_moments_imply_projected
