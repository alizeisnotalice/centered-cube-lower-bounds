import BrownianGridLaw
import FirstCrossValue
open MeasureTheory ProbabilityTheory Set
open scoped NNReal
namespace CubeBrownian

theorem brownian_grid_CDF {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) (c : ℝ)
    {n : ℕ} (t : Fin (n+1) → ℝ≥0) (ht : Monotone t) (a z : ℝ) :
    let D (w : Ω) (i : Fin n) := c*(B (t i.succ) w-B (t i.castSucc) w)
    let E : Set Ω := {w | ∃ k, a < partialSum k (D w)}
    let Z (w : Ω) := ∑ i, D w i
    μ (E ∩ {w | Z w ≤ z}) = μ (E ∩ {w | 2*firstCrossValue a (D w)-Z w ≤ z}) := by
  dsimp only
  let D (w : Ω) (i : Fin n) := c*(B (t i.succ) w-B (t i.castSucc) w)
  let F (x : Fin n → ℝ) := ∑ i, x i
  let E : Set (Fin n → ℝ) := {x | ∃ k, a < partialSum k x}
  let G (x : Fin n → ℝ) := 2*firstCrossValue a x-F x
  let v (i : Fin n) : ℝ≥0 := NNReal.mk (c^2) (sq_nonneg c) *
    nndist (t i.succ).1 (t i.castSucc).1
  have hmD : AEMeasurable D μ := by
    apply aemeasurable_pi_iff.mpr
    intro i
    simpa only [D, Pi.sub_apply] using
      (gaussianReal_const_mul (hB.hasLaw_sub (t i.succ) (t i.castSucc)) c).aemeasurable
  have hmE : MeasurableSet E := by
    change MeasurableSet {x | ∃ k, a < partialSum k x}
    rw [← firstCross_iUnion]
    exact .iUnion (measurable_firstCross a)
  have hmF : Measurable F := Finset.measurable_fun_sum _ (fun i _ ↦ measurable_pi_apply i)
  have hmG : Measurable G :=
    (measurable_const.mul (measurable_firstCrossValue a)).sub hmF
  have H := firstCross_grid_endpoint_CDF v a z (firstCrossValue a)
    (fun _ _ hx ↦ firstCrossValue_eq hx)
  rw [← brownian_gridLaw hB c t ht] at H
  change μ.map D (E ∩ {x | F x ≤ z}) = μ.map D (E ∩ {x | G x ≤ z}) at H
  rw [Measure.map_apply_of_aemeasurable hmD (hmE.inter (measurableSet_le hmF measurable_const)),
      Measure.map_apply_of_aemeasurable hmD (hmE.inter (measurableSet_le hmG measurable_const))] at H
  exact H
end CubeBrownian
#print axioms CubeBrownian.brownian_grid_CDF
