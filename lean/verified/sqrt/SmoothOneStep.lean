import SmoothFaceDerivative
import SmoothTaylor
import CoordinateMomentMatch
import LindebergReplacement

open MeasureTheory
open scoped BigOperators

namespace CubeSqrtProbability

/-- The smooth face test compares one replacement of a projected vector with
its Gaussian companion, using solely the coordinate moments of orders one and
two and the sum of the two third-moment error budgets. -/
theorem exists_smoothFace_one_replacement {ι : Type*} [Fintype ι] [DecidableEq ι] :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (μ ν : Measure (ι → ℝ)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
      (∀ k : ℕ, k = 1 ∨ k = 2 → ∀ r : Fin k → ι,
        Integrable (fun d : ι → ℝ ↦ ∏ j, d (r j)) μ ∧
        Integrable (fun d : ι → ℝ ↦ ∏ j, d (r j)) ν ∧
        (∫ d : ι → ℝ, ∏ j, d (r j) ∂μ) = ∫ d : ι → ℝ, ∏ j, d (r j) ∂ν) →
      Integrable (fun d : ι → ℝ ↦ ‖d‖ ^ 3) μ →
      Integrable (fun d : ι → ℝ ↦ ‖d‖ ^ 3) ν →
      ∀ (c z : ι → ℝ) (t η : ℝ), 0 < η →
      |(∫ d, smoothFaceCutoff c t η (z+d) ∂μ) -
         ∫ d, smoothFaceCutoff c t η (z+d) ∂ν| ≤
        (K / η^3) * ((∫ d : ι → ℝ, ‖d‖ ^ 3 ∂μ) + ∫ d : ι → ℝ, ‖d‖ ^ 3 ∂ν) := by
  obtain ⟨K,hK,hKb⟩ := exists_smoothFace_directional_third_bound (ι := ι)
  refine ⟨K/6, by positivity, ?_⟩
  intro μ ν _ _ hEq hmμ hmν c z t η hη
  let f := smoothFaceCutoff c t η
  let c₀ := f z
  let L := iteratedFDeriv ℝ 1 f z
  let Q := iteratedFDeriv ℝ 2 f z
  let l := fun d : ι → ℝ ↦ L (fun _ ↦ d)
  let q := fun d : ι → ℝ ↦ Q (fun _ ↦ d)/2
  let e := fun d : ι → ℝ ↦ (K/6/η^3)*‖d‖^3
  let F := fun d : ι → ℝ ↦ f (z+d)
  have hf : ContDiff ℝ 3 f := smoothFaceCutoff_contDiff c t η
  have hF (ρ : Measure (ι → ℝ)) [IsProbabilityMeasure ρ] : Integrable F ρ :=
    (integrable_const (1:ℝ)).mono' (hf.continuous.comp (continuous_const.add continuous_id)).aestronglyMeasurable
       (ae_of_all _ fun d ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (smoothFaceCutoff_nonneg c t η (z+d))]
        exact smoothFaceCutoff_le_one c t η (z+d))
  have hLμ := integrable_multilinear_contraction μ id L (fun r ↦ (hEq 1 (.inl rfl) r).1)
  have hLν := integrable_multilinear_contraction ν id L (fun r ↦ (hEq 1 (.inl rfl) r).2.1)
  have hQμ := (integrable_multilinear_contraction μ id Q (fun r ↦ (hEq 2 (.inr rfl) r).1)).div_const (2:ℝ)
  have hQν := (integrable_multilinear_contraction ν id Q (fun r ↦ (hEq 2 (.inr rfl) r).2.1)).div_const (2:ℝ)
  have hL := multilinear_contraction_integral_eq μ ν id id L
    (fun r ↦ (hEq 1 (.inl rfl) r).1) (fun r ↦ (hEq 1 (.inl rfl) r).2.1)
    (fun r ↦ (hEq 1 (.inl rfl) r).2.2)
  have hQ : (∫ d, q d ∂μ) = ∫ d, q d ∂ν := by
    unfold q
    rw [integral_div,integral_div]
    exact congrArg (fun x : ℝ ↦ x/2)
      (multilinear_contraction_integral_eq μ ν id id Q
        (fun r ↦ (hEq 2 (.inr rfl) r).1) (fun r ↦ (hEq 2 (.inr rfl) r).2.1)
        (fun r ↦ (hEq 2 (.inr rfl) r).2.2))
  have hRem (d : ι → ℝ) : |F d - (c₀+l d+q d)| ≤ e d := by
    let g := fun w : ℝ ↦ f (z+w • d)
    have hg : ContDiff ℝ 3 g := hf.comp (by fun_prop)
    have hb (w : ℝ) : |iteratedDeriv 3 g w| ≤ K*(‖d‖/η)^3 := by
      exact hKb c z d t η ‖d‖ hη (norm_nonneg _) (fun i ↦ by
        rw [← Real.norm_eq_abs]
        exact norm_le_pi_norm d i) w
    have he := unit_segment_taylor_second_error g hg _ (fun y _ ↦ hb y)
    have h1 : iteratedDeriv 1 g 0 = l d := iteratedDeriv_line_eq_iteratedFDeriv f 1 (hf.of_le (by norm_num)) z d
    have h2 : iteratedDeriv 2 g 0 = Q (fun _ ↦ d) := iteratedDeriv_line_eq_iteratedFDeriv f 2 (hf.of_le (by norm_num)) z d
    rw [h1,h2] at he
    have ha : K * (‖d‖/η)^3/6 = e d := by
      unfold e
      rw [div_pow]
      ring
    rw [ha] at he
    simpa only [g,one_smul,zero_smul,add_zero,F,c₀,q] using he
  have H := one_replacement_of_matching_moments μ ν F l q e F l q e c₀
    (hF μ) hLμ hQμ (hmμ.const_mul _) (hF ν) hLν hQν (hmν.const_mul _)
    hL hQ (ae_of_all _ hRem) (ae_of_all _ hRem)
  simpa only [F,f,e,integral_const_mul, mul_add] using H

end CubeSqrtProbability
#print axioms CubeSqrtProbability.exists_smoothFace_one_replacement
