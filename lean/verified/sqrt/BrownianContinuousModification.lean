import DyadicContinuousLimit

namespace CubeBrownian
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

noncomputable def brownianDyadicModification {Ω : Type*}
    (B : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  dyadicLimit (fun r => B r ω) t

theorem brownian_dyadic_modification {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ) (hB : IsPreBrownianReal B P)
    (hGrid : ∀ᵐ ω ∂P, DyadicGood (fun r => B r ω))
    (hFixed : ∀ t : ℝ≥0, ∀ᵐ ω ∂P,
      Tendsto (fun m => B (dyadicClock m (dyadicIndex m t)) ω) atTop (𝓝 (B t ω))) :
    IsBrownianReal (brownianDyadicModification B) P where
  toIsPreBrownianReal := hB.congr fun t => by
    filter_upwards [hGrid,hFixed t] with ω hg hf
    exact tendsto_nhds_unique hf (dyadic_approx_tendsto_limit hg t)
  cont := hGrid.mono fun _ hg => dyadicLimit_continuous hg

#print axioms brownian_dyadic_modification
end CubeBrownian
