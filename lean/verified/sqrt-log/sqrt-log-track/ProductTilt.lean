import Mathlib.Probability.Moments.Tilted
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace CubeMD

variable {ι Ω : Type*} [Fintype ι] {mΩ : MeasurableSpace Ω}
variable (μ : ι → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
variable (Y : ι → Ω → ℝ)

theorem tilted_pi_eq_pi_tilted (q : ℝ)
    (hInt : ∀ i, Integrable (fun x ↦ Real.exp (q * Y i x)) (μ i)) :
    (Measure.pi μ).tilted (fun x : ι → Ω ↦ q * ∑ i, Y i (x i)) =
      Measure.pi (fun i ↦ (μ i).tilted (q * Y i ·)) := by
  classical
  let X : (ι → Ω) → ℝ := fun x ↦ ∑ i, Y i (x i)
  let ν : ι → Measure Ω := fun i ↦ (μ i).tilted (q * Y i ·)
  letI : ∀ i, IsProbabilityMeasure (ν i) := fun i ↦ isProbabilityMeasure_tilted (hInt i)
  have hExp (x : ι → Ω) : Real.exp (q * X x) = ∏ i, Real.exp (q * Y i (x i)) := by
    dsimp only [X]
    rw [Finset.mul_sum, Real.exp_sum]
  have hMgf : mgf X (Measure.pi μ) q = ∏ i, mgf (Y i) (μ i) q := by
    simp only [mgf, hExp]
    exact integral_fintype_prod_eq_prod (fun i x ↦ Real.exp (q * Y i x))
  have hFactor (x : ι → Ω) :
      Real.exp (q * X x) / mgf X (Measure.pi μ) q =
        ∏ i, Real.exp (q * Y i (x i)) / mgf (Y i) (μ i) q := by
    rw [hMgf, hExp, ← Finset.prod_div_distrib]
  change (Measure.pi μ).tilted (q * X ·) = Measure.pi ν
  symm
  apply Measure.pi_eq
  intro s hs
  have hs' : MeasurableSet (Set.pi Set.univ s) :=
    MeasurableSet.pi Set.countable_univ (fun i _ ↦ hs i)
  rw [tilted_mul_apply_eq_ofReal_integral_mgf' hs']
  simp only [hFactor, ν, tilted_mul_apply_eq_ofReal_integral_mgf' (hs _)]
  rw [Measure.restrict_pi_pi, integral_fintype_prod_eq_prod
    (fun i x ↦ Real.exp (q * Y i x) / mgf (Y i) (μ i) q)]
  refine ENNReal.ofReal_prod_of_nonneg (fun i _ ↦ ?_)
  apply integral_nonneg
  intro x
  exact div_nonneg (Real.exp_pos _).le (mgf_pos (hInt i)).le

end CubeMD
#print axioms CubeMD.tilted_pi_eq_pi_tilted
