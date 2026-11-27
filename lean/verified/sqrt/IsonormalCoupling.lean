import ExpMaxExpectation
import Mathlib.Probability.Distributions.Gaussian.Fernique
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
namespace CubeBrownian
section
variable {Ω H : Type*} [MeasurableSpace Ω] [SeminormedAddCommGroup H] [NormedSpace ℝ H]

noncomputable def isoVar (k : ℝ≥0) (x : H) : ℝ≥0 :=
  k * NNReal.mk (‖x‖^2) (sq_nonneg _)

noncomputable def isoScore (W : H →ₗ[ℝ] (Ω → ℝ)) (k : ℝ≥0) (x : H) (w : Ω) : ℝ :=
  Real.sqrt (k:ℝ)*W x w - (isoVar k x:ℝ)/2

theorem isoScore_hasLaw (μ : Measure Ω)
    (W : H →ₗ[ℝ] (Ω → ℝ))
    (hW : ∀ x, HasLaw (W x) (gaussianReal 0 (isoVar 1 x)) μ)
    (k : ℝ≥0) (x : H) :
    HasLaw (isoScore W k x) (gaussianReal (-(isoVar k x:ℝ)/2) (isoVar k x)) μ := by
  have h := gaussianReal_const_mul (hW x) (Real.sqrt (k:ℝ))
  have hk : NNReal.mk ((Real.sqrt (k:ℝ))^2) (sq_nonneg _) = k := by
    apply NNReal.eq
    exact Real.sq_sqrt (NNReal.coe_nonneg k)
  have he : k*isoVar 1 x = isoVar k x := by simp [isoVar]
  rw [mul_zero,hk,he] at h
  have h' := gaussianReal_sub_const h ((isoVar k x:ℝ)/2)
  change HasLaw (fun w ↦ Real.sqrt (k:ℝ)*W x w - (isoVar k x:ℝ)/2) _ μ
  simpa only [zero_sub,neg_div] using h'

theorem gaussian_hasLaw_raw_second_moment (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (m : ℝ) (v : ℝ≥0) (hX : HasLaw X (gaussianReal m v) μ) :
    Integrable (fun w ↦ (X w)^2) μ ∧ (∫ w, (X w)^2 ∂μ) = (v:ℝ)+m^2 := by
  have hm : MemLp id 2 (gaussianReal m v) := IsGaussian.memLp_two_id
  have hLp := hX.memLp hm
  have hI := (memLp_two_iff_integrable_sq hX.aemeasurable.aestronglyMeasurable).1 hLp
  have hmean := hX.integral_eq
  rw [integral_id_gaussianReal] at hmean
  have hv := hX.variance_eq
  change ProbabilityTheory.variance X μ = ProbabilityTheory.variance (fun x : ℝ ↦ x) (gaussianReal m v) at hv
  rw [variance_eq_sub hLp,variance_fun_id_gaussianReal,hmean] at hv
  change (∫ w, (X w)^2 ∂μ)-m^2 = (v:ℝ) at hv
  exact ⟨hI, by linarith only [hv]⟩

theorem isoScore_coupled_second_moment (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : H →ₗ[ℝ] (Ω → ℝ))
    (hW : ∀ x, HasLaw (W x) (gaussianReal 0 (isoVar 1 x)) μ)
    (k : ℝ≥0) (x y : H) :
    Integrable (fun w ↦ (isoScore W k x w-isoScore W k y w)^2) μ ∧
    (∫ w, (isoScore W k x w-isoScore W k y w)^2 ∂μ) =
      (isoVar k (x-y):ℝ)+(((isoVar k x:ℝ)-(isoVar k y:ℝ))/2)^2 := by
  let d := ((isoVar k x:ℝ)-(isoVar k y:ℝ))/2
  let Z := fun w ↦ Real.sqrt (k:ℝ)*W (x-y) w - d
  have h := gaussianReal_const_mul (hW (x-y)) (Real.sqrt (k:ℝ))
  have hk : NNReal.mk ((Real.sqrt (k:ℝ))^2) (sq_nonneg _) = k := by
    apply NNReal.eq
    exact Real.sq_sqrt (NNReal.coe_nonneg k)
  have he : k*isoVar 1 (x-y) = isoVar k (x-y) := by simp [isoVar]
  rw [mul_zero,hk,he] at h
  have hZ : HasLaw Z (gaussianReal (-d) (isoVar k (x-y))) μ := by
    simpa only [Z,zero_sub] using gaussianReal_sub_const h d
  have hPoint (w : Ω) : isoScore W k x w-isoScore W k y w = Z w := by
    simp only [isoScore,Z,map_sub,Pi.sub_apply,d]
    ring
  simp_rw [hPoint]
  simpa only [neg_sq,d] using gaussian_hasLaw_raw_second_moment μ (-d) _ hZ
end
end CubeBrownian
#print axioms CubeBrownian.isoScore_coupled_second_moment
