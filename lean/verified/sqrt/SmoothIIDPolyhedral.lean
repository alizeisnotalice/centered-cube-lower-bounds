import SmoothOneStep
import ConvolutionReplacement
import SmoothFaceComparison

open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators

namespace CubeSqrtProbability

/-- Fixed-dimensional mixed-face Berry comparison specialized to sums of iid
vectors. It needs no invertibility of the covariance; only the final scalar
face marginals must be nondegenerate Gaussian. The comparison is uniform in
the thresholds and does not require that the true law put zero mass on them. -/
theorem exists_smooth_iid_polyhedral_bound {ι : Type*} [Fintype ι] [DecidableEq ι] :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (μ ν : Measure (ι → ℝ)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
      (∀ k : ℕ, k = 1 ∨ k = 2 → ∀ r : Fin k → ι,
        Integrable (fun d : ι → ℝ ↦ ∏ j, d (r j)) μ ∧
        Integrable (fun d : ι → ℝ ↦ ∏ j, d (r j)) ν ∧
        (∫ d : ι → ℝ, ∏ j, d (r j) ∂μ) = ∫ d : ι → ℝ, ∏ j, d (r j) ∂ν) →
      Integrable (fun d : ι → ℝ ↦ ‖d‖ ^ 3) μ →
      Integrable (fun d : ι → ℝ ↦ ‖d‖ ^ 3) ν →
      ∀ (n : ℕ) (z c m : ι → ℝ) (v : ι → ℝ≥0),
        (∀ i, v i ≠ 0) →
        (∀ i, (sumLaw ν n).map (fun d : ι → ℝ ↦ z i + d i) = gaussianReal (m i) (v i)) →
        ∀ (strict : ι → Bool) (η : ℝ), 0 < η →
        |(sumLaw μ n).real (faceEvent (fun d ↦ z+d) strict c 0) -
          (sumLaw ν n).real (faceEvent (fun d ↦ z+d) strict c 0)| ≤
            ((n:ℝ)*K/η^3) * ((∫ d : ι → ℝ, ‖d‖^3 ∂μ) + ∫ d : ι → ℝ, ‖d‖^3 ∂ν) +
            η * ∑ i, (√(2*Real.pi*(v i:ℝ)))⁻¹ := by
  obtain ⟨K,hK,hKthm⟩ := exists_smoothFace_one_replacement (ι := ι)
  refine ⟨K,hK,?_⟩
  intro μ ν _ _ hEq hμ hν n z c m v hv hLaw strict η hη
  let err : ℝ := (K/η^3)*((∫ d : ι → ℝ, ‖d‖^3 ∂μ) + ∫ d : ι → ℝ, ‖d‖^3 ∂ν)
  have hm (i : ι) : Measurable (fun d : ι → ℝ ↦ (z+d) i) :=
    measurable_const.add (measurable_pi_apply i)
  have hC (t : ℝ) :
      |(∫ w, smoothFaceCutoff c t η (z+w) ∂(sumLaw μ n)) -
        ∫ w, smoothFaceCutoff c t η (z+w) ∂(sumLaw ν n)| ≤ (n:ℝ)*err := by
    apply sumLaw_shift_comparison μ ν (smoothFaceCutoff c t η)
      (smoothFaceCutoff_contDiff c t η).continuous.measurable 1 err
    · intro x
      rw [abs_of_nonneg (smoothFaceCutoff_nonneg c t η x)]
      exact smoothFaceCutoff_le_one c t η x
    · intro a
      exact hKthm μ ν hEq hμ hν c a t η hη
  have hFin := smooth_face_comparison (sumLaw μ n) (sumLaw ν n)
      (fun d ↦ z+d) (fun d ↦ z+d) hm hm strict c m v hv hLaw hη ((n:ℝ)*err) hC
  convert hFin using 1
  unfold err
  ring

end CubeSqrtProbability
#print axioms CubeSqrtProbability.exists_smooth_iid_polyhedral_bound
