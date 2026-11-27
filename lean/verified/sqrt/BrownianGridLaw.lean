import Mathlib.Probability.BrownianMotion.Basic
import DiscreteGridReflection
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace CubeBrownian

theorem brownian_gridLaw {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) (c : ℝ)
    {n : ℕ} (t : Fin (n+1) → ℝ≥0) (ht : Monotone t) :
    (μ.map fun w (i : Fin n) ↦ c * (B (t i.succ) w-B (t i.castSucc) w)) =
      Measure.pi (fun (i : Fin n) ↦
        gaussianReal 0 (NNReal.mk (c^2) (sq_nonneg c) * nndist (t i.succ).1 (t i.castSucc).1)) := by
  have hLaw (i : Fin n) :
      HasLaw (fun w ↦ c * (B (t i.succ) w-B (t i.castSucc) w))
        (gaussianReal 0 (NNReal.mk (c^2) (sq_nonneg c) * nndist (t i.succ).1 (t i.castSucc).1)) μ := by
    simpa only [mul_zero, Pi.sub_apply] using gaussianReal_const_mul (hB.hasLaw_sub (t i.succ) (t i.castSucc)) c
  have hInd := (hB.hasIndepIncrements n t ht).comp (fun _ (x : ℝ) ↦ c*x) (by fun_prop)
  rw [hInd.map_fun_eq_pi_map (fun i ↦ (hLaw i).aemeasurable)]
  simp only [fun i ↦ (hLaw i).map_eq]
end CubeBrownian
#print axioms CubeBrownian.brownian_gridLaw
