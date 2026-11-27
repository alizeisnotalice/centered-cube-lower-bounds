import PairedFiniteUniform
import CenteredBoxActualPulse

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology RealInnerProductSpace
namespace CubeBrownian

set_option maxHeartbeats 700000
theorem centeredBoxNode_L2_tendsto_filter {α : Type*} {l : Filter α} (e : α→ℝ) (hp : ∀ n, 0<e n)
    (he : Tendsto e l (𝓝 0)) {t : ℝ} (ht : 0≤t) :
    Tendsto (fun n => centeredBoxNodeL2 (e n) t (hp n) ht) l (𝓝 (stepNodeL2 t)) := by
  apply Metric.tendsto_nhds.2
  intro δ hδ
  filter_upwards [he.eventually_lt_const (show 0 < δ^2/2 by positivity)] with n hn
  rw [dist_eq_norm]
  have H := centeredBoxNode_L2_error (hp n) ht
  nlinarith only [H,hn,hδ,norm_nonneg (centeredBoxNodeL2 (e n) t (hp n) ht-stepNodeL2 t)]

/-- Removal of box smoothing for the actual Gaussian grid law. The finite
coupling is built anew on both node families' joint span at every index.
No isonormal Gaussian process on an infinite-dimensional Hilbert space
or across all smoothing widths is assumed. -/
theorem canonical_centeredBox_grid_uniform_Brownian
    {Ω I α : Type*} {l : Filter α} [MeasurableSpace Ω] [Fintype I] [Nonempty I]
    (μ : Measure Ω) (B : ℝ≥0→Ω→ℝ) (hB : IsPreBrownianReal B μ)
    (t : I→ℝ≥0) (e : α→ℝ) (hp : ∀ n, 0<e n) (he : Tendsto e l (𝓝 0))
    (K : ℝ≥0) (δ : ℝ) (hδ : 0<δ) :
    ∀ᶠ n in l, ∀ k : ℝ≥0, k≤K →
      |canonicalFiniteGridExp (fun i => centeredBoxNodeL2 (e n) (t i) (hp n)
          (NNReal.coe_nonneg (t i))) k -
        (∫ x, Real.exp (⨆ i, Real.sqrt (k:ℝ)*B (t i) x-(k:ℝ)*(t i:ℝ)/2) ∂μ)| < δ := by
  have H := canonical_finite_grid_uniform
    (fun n i => centeredBoxNodeL2 (e n) (t i) (hp n) (NNReal.coe_nonneg (t i)))
    (fun i => stepNodeL2 (t i))
    (fun i => centeredBoxNode_L2_tendsto_filter e hp he (NNReal.coe_nonneg (t i))) K δ hδ
  filter_upwards [H] with n hn k hk
  rw [←canonical_stepGrid_eq_Brownian μ B hB t k]
  exact hn k hk

#print axioms canonical_centeredBox_grid_uniform_Brownian
end CubeBrownian
