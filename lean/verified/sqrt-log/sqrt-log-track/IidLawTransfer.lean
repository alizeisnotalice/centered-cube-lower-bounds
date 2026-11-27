import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.Real

open MeasureTheory ProbabilityTheory Set
namespace CubeMD

theorem iid_sum_tail_eq_product {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    [IsProbabilityMeasure ν] {n : ℕ} {X : Fin n → Ω → ℝ}
    (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X ν) {μ : Measure ℝ}
    (hlaw : ∀ i, ν.map (X i) = μ) (m : ℝ) :
    ν.real {ω | m ≤ ∑ i, X i ω} =
      (Measure.pi (fun _ : Fin n ↦ μ)).real {x | m ≤ ∑ i, x i} := by
  let f : Ω → Fin n → ℝ := fun ω i ↦ X i ω
  have hf : Measurable f := measurable_pi_iff.mpr hX
  have hmap : ν.map f = Measure.pi (fun _ : Fin n ↦ μ) := by
    rw [show ν.map f = Measure.pi (fun i ↦ ν.map (X i)) from hind.map_fun_eq_pi_map (fun i ↦ (hX i).aemeasurable)]
    simp only [hlaw]
  have hsum : Measurable (fun x : Fin n → ℝ ↦ ∑ i, x i) :=
    Finset.measurable_fun_sum _ fun i _ ↦ measurable_pi_apply i
  have hs : MeasurableSet {x : Fin n → ℝ | m ≤ ∑ i, x i} :=
    measurableSet_le measurable_const hsum
  rw [← hmap]
  change (ν {ω | m ≤ ∑ i, X i ω}).toReal = ((ν.map f) {x | m ≤ ∑ i, x i}).toReal
  rw [Measure.map_apply hf hs] <;> rfl

end CubeMD
#print axioms CubeMD.iid_sum_tail_eq_product
