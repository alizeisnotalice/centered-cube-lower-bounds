import FiniteWinner
import Mathlib.Probability.Distributions.Gaussian.Real
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
namespace CubeBrownian

theorem gaussian_half_variance_exp_normalized {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {X : Ω → ℝ} {v : ℝ≥0}
    (hX : HasLaw X (gaussianReal (-(v:ℝ)/2) v) μ) :
    ∫ w, Real.exp (X w) ∂μ = 1 := by
  have h := integral_map hX.aemeasurable
    (Real.measurable_exp.aestronglyMeasurable : AEStronglyMeasurable Real.exp (μ.map X))
  change (∫ z, Real.exp z ∂(μ.map X)) = ∫ w, Real.exp (X w) ∂μ at h
  rw [← h,hX.map_eq]
  change (∫ z, Real.exp z ∂(gaussianReal (-(v:ℝ)/2) v)) = _
  calc
    _ = mgf (fun z : ℝ ↦ z) (gaussianReal (-(v:ℝ)/2) v) 1 := by simp [mgf]
    _ = _ := by rw [mgf_fun_id_gaussianReal]; simp; ring_nf

theorem finiteWinner_gaussian_tilted_sum {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {n : ℕ} (hn : 0 < n)
    (X : Fin n → Ω → ℝ) (hm : ∀ i, Measurable (X i))
    (v : Fin n → ℝ≥0)
    (hX : ∀ i, HasLaw (X i) (gaussianReal (-(v i:ℝ)/2) (v i)) μ) :
    (∑ j, (μ.tilted (X j)) (finiteWinner X j)) =
      ∫⁻ w, ENNReal.ofReal (Real.exp (⨆ i, X i w)) ∂μ :=
  finiteWinner_tilted_sum_expMax μ hn X hm (fun i ↦ gaussian_half_variance_exp_normalized (hX i))

end CubeBrownian
#print axioms CubeBrownian.finiteWinner_gaussian_tilted_sum
