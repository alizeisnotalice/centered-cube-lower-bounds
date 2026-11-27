import TrueTiltMean

open MeasureTheory

namespace CubeSqrtProbability

theorem log1p_abs_le {a y : ℝ} (ha : a ≤ 1/2) (hy : |y| ≤ a) :
    |Real.log (1+y)| ≤ 2*|y| := by
  have hq := log1p_quadratic_approx ha hy
  have hnonneg : 0 ≤ a := (abs_nonneg _).trans hy
  have hy2 : y^2 ≤ |y|/2 := by
    rw [← sq_abs]
    nlinarith [mul_nonneg (abs_nonneg y) (show 0 ≤ 1/2-|y| by linarith)]
  calc
    _ = |(Real.log (1+y)-(y-y^2/2))+(y-y^2/2)| := by ring_nf
    _ ≤ |Real.log (1+y)-(y-y^2/2)| + |y-y^2/2| := abs_add_le _ _
    _ ≤ 2*a*y^2+(|y|+y^2/2) := by
      apply add_le_add hq
      calc
        _ ≤ |y|+|y^2/2| := abs_sub _ _
        _ = _ := by rw [abs_of_nonneg (by positivity : 0 ≤ y^2/2)]
    _ ≤ _ := by nlinarith [mul_nonneg (show 0 ≤ 1-2*a by linarith) (sq_nonneg y)]

theorem integrable_of_uniform_abs {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {f : Ω → ℝ} (hm : Measurable f)
    {B : ℝ} (hB : ∀ x, |f x| ≤ B) : Integrable f μ :=
  (integrable_const B).mono' hm.aestronglyMeasurable (ae_of_all _ fun x ↦ by
    simpa only [Real.norm_eq_abs] using hB x)

theorem single_tilt_normalized {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (hmX : Measurable X)
    {a : ℝ} (ha : a ≤ 1/2) (hx : ∀ w, |X w| ≤ a) (hmean : (∫ w, X w ∂μ) = 0) :
    (∫ w, Real.exp (Real.log (1+X w)) ∂μ) = 1 := by
  simp_rw [exp_logPerturbation_eq ha (hx _)]
  rw [integral_add (integrable_const 1) (integrable_of_uniform_abs μ hmX hx), hmean]
  simp

theorem single_tilt_log_integral_exact {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (hmX : Measurable X)
    {a : ℝ} (ha : a ≤ 1/2) (hx : ∀ w, |X w| ≤ a) (hmean : (∫ w, X w ∂μ) = 0)
    (F : Ω → ℝ) :
    (∫ w, F w ∂(μ.tilted (fun w ↦ Real.log (1+X w)))) = ∫ w, (1+X w)*F w ∂μ := by
  rw [integral_tilted, single_tilt_normalized μ X hmX ha hx hmean]
  simp_rw [exp_logPerturbation_eq ha (hx _),div_one,smul_eq_mul]

/-- The manuscript's tilted mean expansion on a genuine probability measure,
with a uniform error linear in the small pointwise load times the variance. -/
theorem single_tilt_log_mean_integrated {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : Ω → ℝ)
    (hmX : Measurable X) (hmY : Measurable Y)
    {a : ℝ} (ha : a ≤ 1/2) (hx : ∀ w, |X w| ≤ a) (hy : ∀ w, |Y w| ≤ a)
    (hmeanX : (∫ w, X w ∂μ) = 0) (hmeanY : (∫ w, Y w ∂μ) = 0) :
    |(∫ w, Real.log (1+Y w) ∂(μ.tilted (fun w ↦ Real.log (1+X w)))) -
       ((∫ w, X w*Y w ∂μ) - (∫ w, Y w^2 ∂μ)/2)| ≤
      4*a*(∫ w, Y w^2 ∂μ) := by
  rw [single_tilt_log_integral_exact μ X hmX ha hx hmeanX]
  have h1 (w : Ω) : 0 ≤ 1+X w := by linarith [(abs_le.mp (hx w)).1]
  have h2 (w : Ω) : 1+X w ≤ 3/2 := by linarith [(abs_le.mp (hx w)).2]
  have hY := integrable_of_uniform_abs μ hmY hy
  have hXY : Integrable (fun w ↦ X w*Y w) μ :=
    integrable_of_uniform_abs μ (hmX.mul hmY) (B := a^2) (fun w ↦ by
      rw [abs_mul,pow_two]
      exact mul_le_mul (hx w) (hy w) (abs_nonneg _) ((abs_nonneg _).trans (hx w)))
  have hYY : Integrable (fun w ↦ Y w^2) μ :=
    integrable_of_uniform_abs μ (hmY.pow_const 2) (fun w ↦ by
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (hy w) _)
  have hG : Integrable (fun w ↦ (1+X w)*Real.log (1+Y w)) μ :=
    integrable_of_uniform_abs μ ((measurable_const.add hmX).mul (Real.measurable_log.comp (measurable_const.add hmY)))
      (B := 3*a) (fun w ↦ by
        rw [abs_mul,abs_of_nonneg (h1 w)]
        calc
          _ ≤ (3/2)*(2*|Y w|) := mul_le_mul (h2 w) (log1p_abs_le ha (hy w)) (abs_nonneg _) (by norm_num)
          _ ≤ _ := by linarith [hy w])
  have hF : Integrable (fun w ↦ Y w+X w*Y w-Y w^2/2) μ :=
    (hY.add hXY).sub (hYY.div_const _)
  have he : (∫ w, (Y w+X w*Y w-Y w^2/2) ∂μ) =
      (∫ w, X w*Y w ∂μ) - (∫ w, Y w^2 ∂μ)/2 := by
    have hSub : (∫ w, (Y w+X w*Y w-Y w^2/2) ∂μ) =
        (∫ w, Y w+X w*Y w ∂μ) - ∫ w, Y w^2/2 ∂μ :=
      integral_sub (hY.add hXY) (hYY.div_const (2:ℝ))
    rw [hSub, integral_add hY hXY,hmeanY,zero_add,integral_div]
  rw [← he, ← integral_sub hG hF]
  refine abs_integral_le_integral_abs.trans ?_
  have hb := integral_mono_ae (hG.sub hF).abs (hYY.const_mul (4*a))
    (ae_of_all μ (fun w ↦ single_tilt_log_mean_pointwise ha (hx w) (hy w)))
  rwa [integral_const_mul] at hb

end CubeSqrtProbability
#print axioms CubeSqrtProbability.single_tilt_log_mean_integrated
