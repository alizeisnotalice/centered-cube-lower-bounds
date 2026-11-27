import TrueTiltRawCovariance

open MeasureTheory

namespace CubeSqrtProbability

noncomputable def logInc {Ω : Type*} (X Y : Ω → ℝ) (w : Ω) :=
  Real.log (1+Y w)-Real.log (1+X w)

theorem abs_sub_of_common_bound {a x y : ℝ} (hx : |x| ≤ a) (hy : |y| ≤ a) :
    |y-x| ≤ 2*a := (abs_sub _ _).trans (by linarith)

theorem single_tilt_raw_increment_covariance {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (W X Y S T : Ω → ℝ)
    (hW : Measurable W) (hX : Measurable X) (hY : Measurable Y)
    (hS : Measurable S) (hT : Measurable T)
    {a : ℝ} (hA : 0 ≤ a) (ha : a ≤ 1/2)
    (hw : ∀ w, |W w| ≤ a) (hx : ∀ w, |X w| ≤ a) (hy : ∀ w, |Y w| ≤ a)
    (hs : ∀ w, |S w| ≤ a) (ht : ∀ w, |T w| ≤ a)
    (hmeanW : (∫ w, W w ∂μ) = 0) :
    |(∫ w, logInc X Y w*logInc S T w ∂(μ.tilted (fun w ↦ Real.log (1+W w)))) -
      ∫ w, (Y w-X w)*(T w-S w) ∂μ| ≤
      5*a*((∫ w, (Y w-X w)^2 ∂μ) + ∫ w, (T w-S w)^2 ∂μ) := by
  rw [single_tilt_log_integral_exact μ W hW ha hw hmeanW]
  let u : Ω → ℝ := fun w ↦ Y w-X w
  let v : Ω → ℝ := fun w ↦ T w-S w
  let g := logInc X Y
  let h := logInc S T
  have mu : Measurable u := hY.sub hX
  have mv : Measurable v := hT.sub hS
  have mg : Measurable g :=
    (Real.measurable_log.comp (measurable_const.add hY)).sub
      (Real.measurable_log.comp (measurable_const.add hX))
  have mh : Measurable h :=
    (Real.measurable_log.comp (measurable_const.add hT)).sub
      (Real.measurable_log.comp (measurable_const.add hS))
  have hu (w : Ω) : |u w| ≤ 2*a := abs_sub_of_common_bound (hx w) (hy w)
  have hv (w : Ω) : |v w| ≤ 2*a := abs_sub_of_common_bound (hs w) (ht w)
  have hg (w : Ω) : |g w| ≤ 4*a := (true_log_increment_bound ha (hx w) (hy w)).trans (by linarith [hu w])
  have hh (w : Ω) : |h w| ≤ 4*a := (true_log_increment_bound ha (hs w) (ht w)).trans (by linarith [hv w])
  have fI : Integrable (fun w ↦ (1+W w)*(g w*h w)) μ :=
    integrable_of_uniform_abs μ ((measurable_const.add hW).mul (mg.mul mh))
      (B := (3/2)*(4*a*(4*a))) (fun w ↦ by
        have hP : 0 ≤ 1+W w := by linarith [(abs_le.mp (hw w)).1]
        have hB : 1+W w ≤ 3/2 := by linarith [(abs_le.mp (hw w)).2]
        rw [abs_mul,abs_of_nonneg hP,abs_mul]
        exact mul_le_mul hB (mul_le_mul (hg w) (hh w) (abs_nonneg _) (by positivity))
          (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (by norm_num))
  have hI : Integrable (fun w ↦ u w*v w) μ :=
    integrable_of_uniform_abs μ (mu.mul mv) (B := (2*a)*(2*a)) (fun w ↦ by
      rw [abs_mul]
      exact mul_le_mul (hu w) (hv w) (abs_nonneg _) (by positivity))
  have iu : Integrable (fun w ↦ (u w)^2) μ :=
    integrable_of_uniform_abs μ (mu.pow_const 2) (B := (2*a)^2)
      (fun w ↦ by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hu w) _)
  have iv : Integrable (fun w ↦ (v w)^2) μ :=
    integrable_of_uniform_abs μ (mv.pow_const 2) (B := (2*a)^2)
      (fun w ↦ by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hv w) _)
  have hpt (w : Ω) : |(1+W w)*(g w*h w)-u w*v w| ≤ 5*a*((u w)^2+(v w)^2) := by
    rw [← mul_assoc]
    exact tilted_two_increment_product_pointwise ha (hw w) (hx w) (hy w) (hs w) (ht w)
  change |(∫ w, (1+W w)*(g w*h w) ∂μ) - (∫ w, u w*v w ∂μ)| ≤ _
  rw [← integral_sub fI hI]
  refine abs_integral_le_integral_abs.trans ?_
  have H := integral_mono_ae (fI.sub hI).abs ((iu.add iv).const_mul (5*a)) (ae_of_all _ hpt)
  rw [integral_const_mul] at H
  exact H.trans_eq (by
    congr 1
    exact integral_add iu iv)

end CubeSqrtProbability
#print axioms CubeSqrtProbability.single_tilt_raw_increment_covariance
