import WeightedTail
import Mathlib.Tactic

open MeasureTheory Set

namespace CubeSqrtProbability

/-- A threshold-uniform probability error survives exponential averaging with
exactly the same coefficient (no threshold-window length factor). -/
theorem exp_weighted_Ioi_comparison (F G : ℝ → ℝ) (ε : ℝ)
    (hF : Measurable F) (hG : Measurable G)
    (hFB : ∀ r, |F r| ≤ 1) (hGB : ∀ r, |G r| ≤ 1)
    (hE : ∀ r > 0, |F r-G r| ≤ ε) :
    |(∫ r in Ioi (0:ℝ), Real.exp (-r)*F r) -
      ∫ r in Ioi (0:ℝ), Real.exp (-r)*G r| ≤ ε := by
  let Q : Measure ℝ := volume.restrict (Ioi (0:ℝ))
  let w : ℝ → ℝ := fun r ↦ Real.exp (-r)
  have hw : Integrable w Q := integrableOn_exp_neg_Ioi 0
  have hw0 (r : ℝ) : 0 ≤ w r := (Real.exp_pos _).le
  have hWF : Integrable (fun r ↦ w r * F r) Q := hw.mono'
      ((Real.measurable_exp.comp measurable_neg).mul hF).aestronglyMeasurable
      (ae_of_all _ fun r ↦ by
        rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (hw0 r)]
        exact mul_le_of_le_one_right (hw0 r) (hFB r))
  have hWG : Integrable (fun r ↦ w r * G r) Q := hw.mono'
      ((Real.measurable_exp.comp measurable_neg).mul hG).aestronglyMeasurable
      (ae_of_all _ fun r ↦ by
        rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (hw0 r)]
        exact mul_le_of_le_one_right (hw0 r) (hGB r))
  change |(∫ r, w r*F r ∂Q) - ∫ r, w r*G r ∂Q| ≤ ε
  rw [← integral_sub hWF hWG]
  refine abs_integral_le_integral_abs.trans ?_
  have hBound (r : ℝ) (hr : r ∈ Ioi (0:ℝ)) :
      |w r * F r - w r * G r| ≤ w r * ε := by
    rw [← mul_sub,abs_mul,abs_of_nonneg (hw0 r)]
    exact mul_le_mul_of_nonneg_left (hE r hr) (hw0 r)
  have he := integral_mono_ae (hWF.sub hWG).abs (hw.mul_const ε)
    ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ hBound))
  refine he.trans_eq ?_
  rw [integral_mul_const]
  change (∫ r in Ioi (0:ℝ), Real.exp (-r))*ε = ε
  rw [integral_exp_neg_Ioi_zero,one_mul]

end CubeSqrtProbability
#print axioms CubeSqrtProbability.exp_weighted_Ioi_comparison
