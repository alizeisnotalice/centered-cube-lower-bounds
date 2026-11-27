import GaussianThirdMoment
import SumLawTransfer

open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators

namespace CubeSqrtProbability

set_option maxHeartbeats 1000000 in
theorem integrable_coordinate_monomial_of_third_norm {ι : Type*} [Fintype ι]
    (ρ : Measure (ι → ℝ)) [IsFiniteMeasure ρ]
    (hρ : Integrable (fun d : ι → ℝ ↦ ‖d‖^3) ρ)
    {k : ℕ} (hk : k ≤ 3) (r : Fin k → ι) :
    Integrable (fun d : ι → ℝ ↦ ∏ j, d (r j)) ρ := by
  have hc : Continuous (fun d : ι → ℝ ↦ ∏ j, d (r j)) :=
    continuous_finsetProd Finset.univ (fun j _ ↦ continuous_apply (r j))
  refine ((integrable_const (1:ℝ)).add hρ).mono' hc.aestronglyMeasurable (ae_of_all _ fun d ↦ ?_)
  have hn : 0 ≤ ‖d‖ := norm_nonneg d
  have hP : ‖∏ j, d (r j)‖ ≤ ‖d‖^k := by
    calc
      _ = ∏ j, ‖d (r j)‖ := by simp only [Real.norm_eq_abs, Finset.abs_prod]
      _ ≤ ∏ _ : Fin k, ‖d‖ := Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) (fun j _ ↦ norm_le_pi_norm d _)
      _ = _ := by simp
  refine hP.trans ?_
  change ‖d‖^k ≤ 1+‖d‖^3
  by_cases h1 : ‖d‖ ≤ 1
  · exact (pow_le_one₀ hn h1).trans (le_add_of_nonneg_right (pow_nonneg hn _))
  · exact (pow_le_pow_right₀ (le_of_not_ge h1) hk).trans (le_add_of_nonneg_left zero_le_one)

theorem integrable_third_norm_of_bound {ι : Type*} [Fintype ι]
    (ρ : Measure (ι → ℝ)) [IsProbabilityMeasure ρ] (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ᵐ d ∂ρ, ‖d‖ ≤ B) :
    Integrable (fun d : ι → ℝ ↦ ‖d‖^3) ρ ∧ (∫ d, ‖d‖^3 ∂ρ) ≤ B^3 := by
  have hR : ∀ᵐ d ∂ρ, ‖d‖^3 ≤ B^3 := hb.mono (fun d hd ↦ pow_le_pow_left₀ (norm_nonneg _) hd _)
  have hh : Integrable (fun d : ι → ℝ ↦ ‖d‖^3) ρ := (integrable_const (B^3)).mono' (by fun_prop)
    (hR.mono (fun d h ↦ by rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg _) _)]; exact h))
  exact ⟨hh, by simpa using integral_mono_ae hh (integrable_const _) hR⟩

/-- Pointwise bound for the actual centered iid law paired with its canonical,
possibly singular Gaussian law, with all moment matching discharged. -/
theorem exists_actual_iid_bounded_face_estimate {ι : Type*} [Fintype ι] [DecidableEq ι] :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (μ : Measure (ι → ℝ)) [IsProbabilityMeasure μ] (B : ℝ), 0 ≤ B →
      (∀ᵐ d ∂μ, ‖d‖ ≤ B) → (∀ i, (∫ d, d i ∂μ) = 0) →
      ∀ (n : ℕ) (z c : ι → ℝ) (strict : ι → Bool) (η : ℝ), 0 < η →
      (∀ i, n • ((rawSecondMoment μ) i i).toNNReal ≠ 0) →
      let S := rawSecondMoment μ
      let ν := centeredGaussianCompanion S
      |(sumLaw μ n).real (faceEvent (fun d ↦ z+d) strict c 0) -
        (sumLaw ν n).real (faceEvent (fun d ↦ z+d) strict c 0)| ≤
          ((n:ℝ)*K/η^3) * (B^3 + stdGaussianThird*∑ i, (√(S i i).toNNReal)^3) +
           η * ∑ i, (√(2*Real.pi*((n • (S i i).toNNReal : ℝ≥0):ℝ)))⁻¹ := by
  obtain ⟨K,hK,hthm⟩ := exists_smooth_iid_polyhedral_bound (ι := ι)
  refine ⟨K,hK,?_⟩
  intro μ _ B hB hb hMean n z c strict η hη hNonzero
  dsimp only
  let S := rawSecondMoment μ
  let ν := centeredGaussianCompanion S
  obtain ⟨hμ,hμbound⟩ := integrable_third_norm_of_bound μ B hB hb
  have hI (i j : ι) : Integrable (fun d : ι → ℝ ↦ d i*d j) μ := by
    let r : Fin 2 → ι := ![i,j]
    simpa [Fin.prod_univ_two,r] using integrable_coordinate_monomial_of_third_norm μ hμ (by omega) r
  have hS : S.PosSemidef := posSemidef_rawSecondMoment μ hI
  have hl (i : ι) : ν.map (fun d ↦ d i) = gaussianReal 0 (S i i).toNNReal :=
    centeredGaussianCompanion_marginal S hS i
  obtain ⟨hν,hνbound⟩ := gaussian_marginal_third_norm_bound ν (fun i ↦ (S i i).toNNReal) hl
  have hEq (k : ℕ) (hk : k = 1 ∨ k = 2) (r : Fin k → ι) :
      (∫ d : ι → ℝ, ∏ j, d (r j) ∂μ) = ∫ d : ι → ℝ, ∏ j, d (r j) ∂ν := by
    rcases hk with rfl | rfl
    · simp [Fin.prod_univ_one,hMean,centeredGaussianCompanion_mean S hS,ν]
    · rw [show (fun d : ι → ℝ ↦ ∏ j, d (r j)) = (fun d ↦ d (r 0)*d (r 1))
          by funext d; simp [Fin.prod_univ_two]]
      exact (centeredGaussianCompanion_second_moment S hS (r 0) (r 1)).symm
  have hh := hthm μ ν
    (fun k hk r ↦ ⟨integrable_coordinate_monomial_of_third_norm μ hμ (by omega) r,
      integrable_coordinate_monomial_of_third_norm ν hν (by omega) r, hEq k hk r⟩)
    hμ hν n z c z (fun i ↦ n • (S i i).toNNReal) hNonzero
    (fun i ↦ sumLaw_shiftedGaussian_marginal S hS i n (z i)) strict η hη
  refine hh.trans (add_le_add ?_ (le_refl _))
  exact mul_le_mul_of_nonneg_left (add_le_add hμbound hνbound) (by positivity)

end CubeSqrtProbability
#print axioms CubeSqrtProbability.exists_actual_iid_bounded_face_estimate
