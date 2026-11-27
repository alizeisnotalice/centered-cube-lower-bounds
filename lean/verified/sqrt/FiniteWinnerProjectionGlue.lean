import FiniteGaussianWinnerCoordinate
import FiniteProjectedMoments

open MeasureTheory ProbabilityTheory Filter WithLp
open scoped NNReal ENNReal Topology ProbabilityTheory RealInnerProductSpace
namespace CubeSqrtProbability

private theorem dual_euclid_formula {k : ℕ} (L : StrongDual ℝ (EuclideanSpace ℝ (Fin k)))
    (x : EuclideanSpace ℝ (Fin k)) :
    L x = ∑ i, L (EuclideanSpace.basisFun (Fin k) ℝ i) * x i := by
  let B := EuclideanSpace.basisFun (Fin k) ℝ
  have hB : (∑ i, x i • B i) = x := by simpa [B, EuclideanSpace.basisFun_repr] using B.sum_repr x
  conv_lhs => rw [← hB]
  simp [B,mul_comm]

theorem finite_euclid_covariance_dual {Ω : Type*} [MeasurableSpace Ω]
    {k : ℕ} (P : Measure Ω) [IsFiniteMeasure P]
    (Z : Ω → ℝ) (D : Ω → EuclideanSpace ℝ (Fin k))
    (hZ : MemLp Z 2 P) (hD : ∀ i, MemLp (fun w ↦ D w i) 2 P)
    (L : StrongDual ℝ (EuclideanSpace ℝ (Fin k))) :
    covariance Z (L ∘ D) P =
      ∑ i, L (EuclideanSpace.basisFun (Fin k) ℝ i) * covariance Z (fun w ↦ D w i) P := by
  have he : L ∘ D = fun w ↦ ∑ i, L (EuclideanSpace.basisFun (Fin k) ℝ i)*D w i := by
    funext w
    exact dual_euclid_formula L (D w)
  rw [he, covariance_fun_sum_right (fun i ↦ (hD i).const_mul
    (L (EuclideanSpace.basisFun (Fin k) ℝ i))) hZ]
  simp_rw [covariance_const_mul_right]

theorem finite_euclid_regression_vector {Ω : Type*} [MeasurableSpace Ω]
    {k : ℕ} (P : Measure Ω) [IsFiniteMeasure P]
    (Z : Ω → ℝ) (D : Ω → EuclideanSpace ℝ (Fin k))
    (hZ : MemLp Z 2 P) (hD : ∀ i, MemLp (fun w ↦ D w i) 2 P)
    (hv : variance Z P ≠ 0) :
    ∃ c : EuclideanSpace ℝ (Fin k), ∀ L : StrongDual ℝ (EuclideanSpace ℝ (Fin k)),
      covariance Z (L ∘ D) P = L c * variance Z P := by
  refine ⟨toLp 2 (fun i ↦ covariance Z (fun w ↦ D w i) P/variance Z P),fun L ↦ ?_⟩
  rw [finite_euclid_covariance_dual P Z D hZ hD, dual_euclid_formula, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  change _ = (_ * (_/variance Z P))*variance Z P
  field_simp

end CubeSqrtProbability
#print axioms CubeSqrtProbability.finite_euclid_covariance_dual
#print axioms CubeSqrtProbability.finite_euclid_regression_vector
