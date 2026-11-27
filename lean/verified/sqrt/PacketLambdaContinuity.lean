import CanonicalGridScale

open Filter MeasureTheory CubeBrownian
open scoped NNReal Topology
namespace CubeSqrtProbability

/-- Separate the finite Gaussian scale limit from the actual source
elaboration. No simplification of Real numerals is needed. -/
theorem packet_ref_scale_tendsto {H I : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Fintype I] [Nonempty I]
    (f : I → H) (L : ℕ → ℝ) {y : ℝ} (hy : 0 < y)
    (hL : Tendsto L atTop (𝓝 y)) :
    Tendsto (fun n ↦ canonicalFiniteGridExp f ((58/(9*(L n)^2):ℝ).toNNReal))
      atTop (𝓝 (canonicalFiniteGridExp f ((58/(9*y^2):ℝ).toNNReal))) := by
  have hD : Tendsto (fun n ↦ 9*(L n)^2) atTop (𝓝 (9*y^2)) :=
    (hL.pow 2).const_mul (9:ℝ)
  have hC : Tendsto (fun n ↦ (58:ℝ)/(9*(L n)^2)) atTop (𝓝 ((58:ℝ)/(9*y^2))) :=
    tendsto_const_nhds.div hD (by positivity)
  have hNN := (continuous_real_toNNReal.tendsto _).comp hC
  exact ((canonicalFiniteGridExp_continuous_scale f).tendsto _).comp hNN

end CubeSqrtProbability
#print axioms CubeSqrtProbability.packet_ref_scale_tendsto
