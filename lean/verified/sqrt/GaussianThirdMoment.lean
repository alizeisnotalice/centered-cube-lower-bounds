import SmoothIIDPolyhedral
import Mathlib.Probability.Distributions.Gaussian.Multivariate

open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators

namespace CubeSqrtProbability

noncomputable def stdGaussianThird : ℝ := ∫ x : ℝ, |x|^3 ∂(gaussianReal 0 1)

theorem stdGaussianThird_nonneg : 0 ≤ stdGaussianThird :=
  integral_nonneg (fun _ ↦ pow_nonneg (abs_nonneg _) _)

theorem centered_gaussian_third_abs_exact (v : ℝ≥0) :
    (∫ x : ℝ, |x|^3 ∂(gaussianReal 0 v)) = stdGaussianThird*(√(v:ℝ))^3 := by
  let s := √(v:ℝ)
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : NNReal.mk (s^2) (sq_nonneg s) = v :=
    NNReal.eq (Real.sq_sqrt v.coe_nonneg)
  have hm := gaussianReal_map_const_mul (μ := 0) (v := 1) s
  rw [mul_zero,mul_one,hs2] at hm
  rw [← hm,integral_map (by fun_prop) (by fun_prop)]
  simp_rw [abs_mul, abs_of_nonneg hs, mul_pow, integral_const_mul, stdGaussianThird]
  ring

theorem norm_pi_cube_le_sum_abs_cube {ι : Type*} [Fintype ι] (d : ι → ℝ) :
    ‖d‖^3 ≤ ∑ i, |d i|^3 := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl h =>
    letI := h
    rw [Subsingleton.elim d (0 : ι → ℝ)]
    simp
  | inr h =>
    letI := h
    obtain ⟨i,hi,hmax⟩ := Finset.exists_max_image (Finset.univ : Finset ι)
       (fun i ↦ ‖d i‖) Finset.univ_nonempty
    have hn : ‖d‖ ≤ ‖d i‖ :=
      (pi_norm_le_iff_of_nonneg (norm_nonneg _) : ‖d‖ ≤ ‖d i‖ ↔ _).2
        (fun j ↦ hmax j (Finset.mem_univ j))
    calc
      _ ≤ ‖d i‖^3 := pow_le_pow_left₀ (norm_nonneg _) hn _
      _ = |d i|^3 := by rw [Real.norm_eq_abs]
      _ ≤ _ := Finset.single_le_sum (fun j _ ↦ pow_nonneg (abs_nonneg (d j)) 3) hi

/-- Only scalar marginal laws are required for this third norm moment bound.
In particular the joint Gaussian law may be singular. -/
theorem gaussian_marginal_third_norm_bound {ι : Type*} [Fintype ι]
    (ν : Measure (ι → ℝ)) [IsProbabilityMeasure ν] (v : ι → ℝ≥0)
    (hLaw : ∀ i, ν.map (fun d : ι → ℝ ↦ d i) = gaussianReal 0 (v i)) :
    Integrable (fun d : ι → ℝ ↦ ‖d‖^3) ν ∧
      (∫ d : ι → ℝ, ‖d‖^3 ∂ν) ≤ stdGaussianThird * ∑ i, (√(v i:ℝ))^3 := by
  have hI (i : ι) : Integrable (fun d : ι → ℝ ↦ |d i|^3) ν := by
    have hG : Integrable (fun x : ℝ ↦ |x|^3) (gaussianReal 0 (v i)) := by
      simpa only [id_eq, Real.norm_eq_abs] using
        (memLp_id_gaussianReal (μ := 0) (v := v i) 3).integrable_norm_pow' (p := 3)
    rw [← hLaw i] at hG
    exact (integrable_map_measure ((continuous_abs.pow 3).aestronglyMeasurable)
      (measurable_pi_apply i).aemeasurable).mp hG
  have hSum : Integrable (fun d : ι → ℝ ↦ ∑ i, |d i|^3) ν :=
    integrable_finsetSum _ (fun i _ ↦ hI i)
  have hN : Integrable (fun d : ι → ℝ ↦ ‖d‖^3) ν := hSum.mono' (by fun_prop)
    (ae_of_all _ fun d ↦ by
      rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (norm_nonneg d) _)]
      exact norm_pi_cube_le_sum_abs_cube d)
  refine ⟨hN,?_⟩
  calc
    _ ≤ ∫ d : ι → ℝ, ∑ i, |d i|^3 ∂ν :=
      integral_mono hN hSum norm_pi_cube_le_sum_abs_cube
    _ = _ := by
      rw [integral_finsetSum _ (fun i _ ↦ hI i),Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      have he : (∫ d : ι → ℝ, |d i|^3 ∂ν) =
          ∫ x : ℝ, |x|^3 ∂(gaussianReal 0 (v i)) := by
        rw [← hLaw i]
        exact (integral_map (μ := ν) (φ := fun d : ι → ℝ ↦ d i)
          (measurable_pi_apply i).aemeasurable (f := fun x : ℝ ↦ |x|^3)
          (continuous_abs.pow 3).aestronglyMeasurable).symm
      rw [he,centered_gaussian_third_abs_exact]

end CubeSqrtProbability
#print axioms CubeSqrtProbability.gaussian_marginal_third_norm_bound
