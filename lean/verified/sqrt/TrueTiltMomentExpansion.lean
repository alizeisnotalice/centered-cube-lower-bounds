import TrueTiltIntegratedCovariance
import Mathlib.Probability.Moments.Covariance

open MeasureTheory ProbabilityTheory

namespace CubeSqrtProbability

theorem single_tilt_log_difference_mean {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : Ω → ℝ)
    (hX : Measurable X) (hY : Measurable Y)
    {a : ℝ} (ha : a ≤ 1/2) (hx : ∀ w, |X w| ≤ a) (hy : ∀ w, |Y w| ≤ a)
    (hmX : (∫ w, X w ∂μ) = 0) (hmY : (∫ w, Y w ∂μ) = 0) :
    let Q := μ.tilted (fun w ↦ Real.log (1+X w))
    |(∫ w, logInc X Y w ∂Q) + (∫ w, (Y w-X w)^2 ∂μ)/2| ≤
      4*a*((∫ w, X w^2 ∂μ) + ∫ w, Y w^2 ∂μ) := by
  let Q := μ.tilted (fun w ↦ Real.log (1+X w))
  have hiX : Integrable (fun w ↦ Real.exp (Real.log (1+X w))) μ := by
    simp_rw [exp_logPerturbation_eq ha (hx _)]
    exact (integrable_const 1).add (integrable_of_uniform_abs μ hX hx)
  letI : IsProbabilityMeasure Q := isProbabilityMeasure_tilted hiX
  have hi (Z : Ω → ℝ) (hZ : Measurable Z) (hz : ∀ w, |Z w| ≤ a) :
      Integrable (fun w ↦ Real.log (1+Z w)) Q :=
    integrable_of_uniform_abs Q (Real.measurable_log.comp (measurable_const.add hZ))
      (B := 2*a) (fun w ↦ (log1p_abs_le ha (hz w)).trans (by linarith [hz w]))
  have h2 (Z : Ω → ℝ) (hZ : Measurable Z) (hz : ∀ w, |Z w| ≤ a) :
      Integrable (fun w ↦ Z w^2) μ :=
    integrable_of_uniform_abs μ (hZ.pow_const 2) (B := a^2) (fun w ↦ by
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (hz w) _)
  have hp : Integrable (fun w ↦ X w*Y w) μ :=
    integrable_of_uniform_abs μ (hX.mul hY) (B := a^2) (fun w ↦ by
      rw [abs_mul,pow_two]
      exact mul_le_mul (hx w) (hy w) (abs_nonneg _) ((abs_nonneg _).trans (hx w)))
  have hD : (∫ w, (Y w-X w)^2 ∂μ) =
      (∫ w, X w^2 ∂μ)+(∫ w, Y w^2 ∂μ)-2*(∫ w, X w*Y w ∂μ) := by
    simp_rw [show ∀ w, (Y w-X w)^2 = (X w^2+Y w^2)-2*(X w*Y w) by intro w; ring]
    have he : (∫ w, ((X w^2+Y w^2)-2*(X w*Y w)) ∂μ) =
        (∫ w, (X w^2+Y w^2) ∂μ) - ∫ w, 2*(X w*Y w) ∂μ :=
      integral_sub ((h2 X hX hx).add (h2 Y hY hy)) (hp.const_mul 2)
    rw [he,integral_add (h2 X hX hx) (h2 Y hY hy),integral_const_mul]
  have hYb := single_tilt_log_mean_integrated μ X Y hX hY ha hx hy hmX hmY
  have hXb := single_tilt_log_mean_integrated μ X X hX hX ha hx hx hmX hmX
  simp_rw [← pow_two] at hXb
  change |(∫ w, logInc X Y w ∂Q) + (∫ w, (Y w-X w)^2 ∂μ)/2| ≤ _
  have hd : (∫ w, logInc X Y w ∂Q) =
      (∫ w, Real.log (1+Y w) ∂Q) - ∫ w, Real.log (1+X w) ∂Q :=
    integral_sub (hi Y hY hy) (hi X hX hx)
  rw [hd,hD]
  have hE : ((∫ w, Real.log (1+Y w) ∂Q) - ∫ w, Real.log (1+X w) ∂Q) +
        ((∫ w, X w^2 ∂μ)+(∫ w, Y w^2 ∂μ)-2*(∫ w, X w*Y w ∂μ))/2 =
      ((∫ w, Real.log (1+Y w) ∂Q) - ((∫ w, X w*Y w ∂μ) - (∫ w, Y w^2 ∂μ)/2)) -
      ((∫ w, Real.log (1+X w) ∂Q) - ((∫ w, X w^2 ∂μ) - (∫ w, X w^2 ∂μ)/2)) := by ring
  rw [hE]
  calc
    _ ≤ _ := abs_sub _ _
    _ ≤ 4*a*(∫ w, Y w^2 ∂μ)+4*a*(∫ w, X w^2 ∂μ) := add_le_add hYb hXb
    _ = _ := by ring

end CubeSqrtProbability
#print axioms CubeSqrtProbability.single_tilt_log_difference_mean
