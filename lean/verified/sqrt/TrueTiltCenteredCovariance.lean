import TrueTiltMomentExpansion
import Mathlib.Probability.Moments.Covariance

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace CubeSqrtProbability

theorem center_covariance_error {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q] (G H : Ω → ℝ)
    (hG : MemLp G 2 Q) (hH : MemLp H 2 Q)
    (m e : ℝ) (hRaw : |(∫ w, G w*H w ∂Q)-m| ≤ e) :
    |covariance G H Q-m| ≤ e + |(∫ w, G w ∂Q)| * |(∫ w, H w ∂Q)| := by
  rw [covariance_eq_sub hG hH]
  have he : (∫ w, (G*H) w ∂Q) - (∫ w, G w ∂Q)*(∫ w, H w ∂Q)-m =
      ((∫ w, G w*H w ∂Q)-m) - (∫ w, G w ∂Q)*(∫ w, H w ∂Q) := by
    change (∫ w, G w*H w ∂Q) - _ - _ = _
    ring
  rw [he]
  exact (abs_sub _ _).trans (by rw [abs_mul]; exact add_le_add hRaw (le_refl _))

theorem true_single_tilt_centered_increment_covariance {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (W X Y S T : Ω → ℝ)
    (hW : Measurable W) (hX : Measurable X) (hY : Measurable Y)
    (hS : Measurable S) (hT : Measurable T)
    {a : ℝ} (hA : 0 ≤ a) (ha : a ≤ 1/2)
    (hw : ∀ w, |W w| ≤ a) (hx : ∀ w, |X w| ≤ a) (hy : ∀ w, |Y w| ≤ a)
    (hs : ∀ w, |S w| ≤ a) (ht : ∀ w, |T w| ≤ a)
    (hmeanW : (∫ w, W w ∂μ) = 0) :
    let Q := μ.tilted (fun w ↦ Real.log (1+W w))
    |covariance (logInc X Y) (logInc S T) Q -
      ∫ w, (Y w-X w)*(T w-S w) ∂μ| ≤
      5*a*((∫ w, (Y w-X w)^2 ∂μ) + ∫ w, (T w-S w)^2 ∂μ) +
      |(∫ w, logInc X Y w ∂Q)| * |(∫ w, logInc S T w ∂Q)| := by
  let Q := μ.tilted (fun w ↦ Real.log (1+W w))
  have hiW : Integrable (fun w ↦ Real.exp (Real.log (1+W w))) μ := by
    simp_rw [exp_logPerturbation_eq ha (hw _)]
    exact (integrable_const 1).add (integrable_of_uniform_abs μ hW hw)
  letI : IsProbabilityMeasure Q := isProbabilityMeasure_tilted hiW
  have L (B C : Ω → ℝ) (hB : Measurable B) (hC : Measurable C)
      (hb : ∀ w, |B w| ≤ a) (hc : ∀ w, |C w| ≤ a) :
      MemLp (logInc B C) 2 Q := by
    have hM : Measurable (logInc B C) :=
      (Real.measurable_log.comp (measurable_const.add hC)).sub
        (Real.measurable_log.comp (measurable_const.add hB))
    refine MemLp.of_bound hM.aestronglyMeasurable (4*a) (ae_of_all _ fun w ↦ ?_)
    rw [Real.norm_eq_abs]
    exact (true_log_increment_bound ha (hb w) (hc w)).trans
      (by linarith [abs_sub_of_common_bound (hb w) (hc w)])
  exact center_covariance_error Q (logInc X Y) (logInc S T)
    (L X Y hX hY hx hy) (L S T hS hT hs ht) _ _
    (single_tilt_raw_increment_covariance μ W X Y S T hW hX hY hS hT hA ha hw hx hy hs ht hmeanW)

end CubeSqrtProbability
#print axioms CubeSqrtProbability.true_single_tilt_centered_increment_covariance
