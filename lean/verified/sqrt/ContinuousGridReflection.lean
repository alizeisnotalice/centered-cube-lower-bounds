import DiscreteReflection
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace CubeBrownian

theorem crossing_overshoot_tendsto {α : Type*} [MetricSpace α]
    {S : Set α} (hS : IsCompact S) (f : α → ℝ) (hf : ContinuousOn f S)
    (a : ℝ) (before after : ℕ → α)
    (hb : ∀ᶠ n in atTop, before n ∈ S ∧ after n ∈ S ∧ f (before n) ≤ a ∧ a < f (after n))
    (hd : Tendsto (fun n ↦ dist (after n) (before n)) atTop (𝓝 0)) :
    Tendsto (fun n ↦ f (after n)) atTop (𝓝 a) := by
  refine Metric.tendsto_nhds.2 fun ε hε ↦ ?_
  obtain ⟨δ,hδ,hU⟩ := Metric.uniformContinuousOn_iff.mp (hS.uniformContinuousOn_of_continuous hf) ε hε
  have hh := Metric.tendsto_nhds.mp hd δ hδ
  filter_upwards [hb,hh] with n hn hclose
  have hF := hU (after n) hn.2.1 (before n) hn.1 (by simpa only [Real.dist_eq, sub_zero, abs_of_nonneg dist_nonneg] using hclose)
  rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hn.2.2.2)]
  rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (hn.2.2.1.trans hn.2.2.2.le))] at hF
  linarith only [hF,hn.2.2.1]
end CubeBrownian
#print axioms CubeBrownian.crossing_overshoot_tendsto
