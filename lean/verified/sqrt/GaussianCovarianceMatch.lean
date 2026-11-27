import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.HasLaw
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators NNReal

namespace CubeSqrtProbability

noncomputable def rawSecondMoment {ι : Type*} [Fintype ι] (μ : Measure (ι → ℝ)) :
    Matrix ι ι ℝ :=
  fun i j ↦ ∫ d, d i * d j ∂μ

theorem posSemidef_rawSecondMoment {ι : Type*} [Fintype ι]
    (μ : Measure (ι → ℝ)) (hI : ∀ i j, Integrable (fun d : ι → ℝ ↦ d i*d j) μ) :
    (rawSecondMoment μ).PosSemidef := by
  classical
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  constructor
  · ext i j
    simp [Matrix.conjTranspose_apply, rawSecondMoment, mul_comm]
  · intro x
    simp only [Matrix.mulVec, dotProduct, Pi.star_apply, star_trivial, Finset.mul_sum, rawSecondMoment]
    have h (i j : ι) : x i * ((∫ d : ι → ℝ, d i*d j ∂μ)*x j) =
        ∫ d : ι → ℝ, x i * (d i*d j*x j) ∂μ := by
      rw [integral_const_mul,integral_mul_const]
    simp_rw [h]
    have hi (i j : ι) : Integrable (fun d : ι → ℝ ↦ x i * (d i*d j*x j)) μ :=
      ((hI i j).mul_const _).const_mul _
    simp_rw [← integral_finsetSum Finset.univ (fun j _ ↦ hi _ j)]
    rw [← integral_finsetSum Finset.univ (fun i _ ↦ integrable_finsetSum _ (fun j _ ↦ hi i j))]
    apply integral_nonneg
    intro d
    have hs : (∑ i, x i*d i)^2 ≥ 0 := sq_nonneg _
    rw [pow_two, Finset.sum_mul] at hs
    simp_rw [Finset.mul_sum] at hs
    convert hs using 1
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring

end CubeSqrtProbability
#print axioms CubeSqrtProbability.posSemidef_rawSecondMoment
