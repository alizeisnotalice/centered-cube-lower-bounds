import BrownianExpectation
open MeasureTheory Set Filter
open scoped Topology
namespace CubeBrownian

theorem strict_sup_event_eq_iUnion {Ω : Type*} (F : ℕ → Ω → ℝ)
    (hB : ∀ w, BddAbove (Set.range (fun k ↦ F k w))) (x : ℝ) :
    {w | x < ⨆ k, F k w} = ⋃ k, {w | x < F k w} := by
  ext w
  simp only [mem_setOf_eq, mem_iUnion]
  exact lt_ciSup_iff (hB w)

theorem measurable_nat_sup {Ω : Type*} [MeasurableSpace Ω] (F : ℕ → Ω → ℝ)
    (hF : ∀ n, Measurable (F n))
    (hB : ∀ w, BddAbove (Set.range (fun k ↦ F k w))) :
    Measurable (fun w ↦ ⨆ k, F k w) := by
  apply measurable_of_Ioi
  intro x
  change MeasurableSet {w | x < ⨆ k, F k w}
  rw [strict_sup_event_eq_iUnion F hB x]
  exact MeasurableSet.iUnion fun n ↦ measurableSet_lt measurable_const (hF n)
end CubeBrownian
