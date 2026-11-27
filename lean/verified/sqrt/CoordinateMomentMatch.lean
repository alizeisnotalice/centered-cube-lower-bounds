import DirectionalMoments
import Mathlib.LinearAlgebra.Multilinear.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open MeasureTheory
open scoped BigOperators

namespace CubeSqrtProbability

theorem multilinear_coordinate_expand {ι : Type*} [Fintype ι] [DecidableEq ι]
    {k : ℕ} (M : ContinuousMultilinearMap ℝ (fun _ : Fin k ↦ ι → ℝ) ℝ)
    (d : ι → ℝ) :
    M (fun _ ↦ d) =
      ∑ r : Fin k → ι, (∏ j, d (r j)) * M (fun j ↦ Pi.single (r j) 1) := by
  let A (i : ι) : ι → ℝ := Pi.single i 1
  have hA (i : ι) : (d i) • A i = Pi.single i (d i) := by
    simpa [A, smul_eq_mul] using (Pi.single_smul' i (d i) (1:ℝ)).symm
  have hsum : (∑ i, (d i) • A i) = d := by
    simp_rw [hA]
    exact LinearMap.sum_single_apply (fun _ : ι ↦ ℝ) d
  calc
    _ = M.toMultilinearMap (fun _ ↦ ∑ i, d i • A i) := by simp [hsum]
    _ = ∑ r : Fin k → ι, M.toMultilinearMap (fun j ↦ d (r j) • A (r j)) :=
      M.toMultilinearMap.map_sum (fun _ (i : ι) ↦ d i • A i)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r _
      rw [M.toMultilinearMap.map_smul_univ]
      rfl

/-- Coordinate mixed moments determine all matching multilinear contractions
of the same degree. No nonsingularity of the covariance is assumed. -/
theorem multilinear_contraction_integral_eq {Ω Ω' ι : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] [Fintype ι] [DecidableEq ι]
    (μ : Measure Ω) (ν : Measure Ω') (X : Ω → ι → ℝ) (G : Ω' → ι → ℝ)
    {k : ℕ} (M : ContinuousMultilinearMap ℝ (fun _ : Fin k ↦ ι → ℝ) ℝ)
    (hX : ∀ r : Fin k → ι, Integrable (fun w ↦ ∏ j, X w (r j)) μ)
    (hG : ∀ r : Fin k → ι, Integrable (fun w ↦ ∏ j, G w (r j)) ν)
    (hEq : ∀ r : Fin k → ι, (∫ w, ∏ j, X w (r j) ∂μ) = ∫ w, ∏ j, G w (r j) ∂ν) :
    (∫ w, M (fun _ ↦ X w) ∂μ) = ∫ w, M (fun _ ↦ G w) ∂ν := by
  simp_rw [multilinear_coordinate_expand M]
  rw [integral_finsetSum _ (fun r _ ↦ (hX r).mul_const (M _)),
      integral_finsetSum _ (fun r _ ↦ (hG r).mul_const (M _))]
  apply Finset.sum_congr rfl
  intro r _
  rw [integral_mul_const,integral_mul_const,hEq r]

theorem integrable_multilinear_contraction {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    (μ : Measure Ω) (X : Ω → ι → ℝ) {k : ℕ}
    (M : ContinuousMultilinearMap ℝ (fun _ : Fin k ↦ ι → ℝ) ℝ)
    (hX : ∀ r : Fin k → ι, Integrable (fun w ↦ ∏ j, X w (r j)) μ) :
    Integrable (fun w ↦ M (fun _ ↦ X w)) μ := by
  simp_rw [multilinear_coordinate_expand M]
  exact integrable_finsetSum _ (fun r _ ↦ (hX r).mul_const (M _))

end CubeSqrtProbability
#print axioms CubeSqrtProbability.multilinear_contraction_integral_eq
