import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.CDF
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace CubeBrownian

noncomputable def Φ (x : ℝ) : ℝ := cdf (gaussianReal 0 1) x
noncomputable def φ (x : ℝ) : ℝ := gaussianPDFReal 0 1 x
noncomputable def maxExpFormula (T : ℝ) : ℝ :=
  (T+2)*Φ (Real.sqrt (T/2)) + Real.sqrt (2*T)*φ (Real.sqrt (T/2))

theorem phi_bounded (x : ℝ) : 0 ≤ φ x ∧ φ x ≤ (Real.sqrt (2*Real.pi))⁻¹ := by
  refine ⟨gaussianPDFReal_nonneg _ _ _,?_⟩
  unfold φ
  rw [gaussianPDFReal_def]
  simp only [NNReal.coe_one, mul_one, sub_zero]
  have hn : (-(x^2))/2 ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by norm_num)
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr hn)
      (show 0 ≤ (Real.sqrt (2*Real.pi))⁻¹ by positivity)

theorem maxExpFormula_div_tendsto_one :
    Tendsto (fun T : ℝ ↦ maxExpFormula T/T) atTop (𝓝 1) := by
  have ht : Tendsto (fun T : ℝ ↦ T/2) atTop atTop := by
    simpa only [div_eq_mul_inv,id_eq] using
      (tendsto_id.atTop_mul_const (show 0 < (2:ℝ)⁻¹ by norm_num))
  have hΦ : Tendsto (fun T : ℝ ↦ Φ (Real.sqrt (T/2))) atTop (𝓝 1) :=
    (tendsto_cdf_atTop (gaussianReal 0 1)).comp (Real.tendsto_sqrt_atTop.comp ht)
  have hfac : Tendsto (fun T : ℝ ↦ 1+2/T) atTop (𝓝 1) := by
    simpa only [add_zero,id_eq] using
      (tendsto_const_nhds (x := (1:ℝ))).add ((tendsto_const_nhds (x := (2:ℝ))).div_atTop tendsto_id)
  have hdec : Tendsto (fun T : ℝ ↦ Real.sqrt (2:ℝ)/Real.sqrt T*(Real.sqrt (2*Real.pi))⁻¹)
      atTop (𝓝 0) := by
    simpa only [zero_mul] using
      ((tendsto_const_nhds (x := Real.sqrt (2:ℝ))).div_atTop Real.tendsto_sqrt_atTop).mul
        (tendsto_const_nhds (x := (Real.sqrt (2*Real.pi))⁻¹))
  have htpos : ∀ᶠ T : ℝ in atTop, 0 < T := eventually_gt_atTop 0
  have hsmall : Tendsto (fun T : ℝ ↦ Real.sqrt (2*T)/T*φ (Real.sqrt (T/2))) atTop (𝓝 0) := by
    apply squeeze_zero' _ _ hdec
    · filter_upwards [htpos] with T hT
      exact mul_nonneg (div_nonneg (Real.sqrt_nonneg _) hT.le) (phi_bounded _).1
    · filter_upwards [htpos] with T hT
      have hs : Real.sqrt (2*T)/T = Real.sqrt 2 / Real.sqrt T := by
        rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
        have hsq := Real.sq_sqrt hT.le
        have hz : Real.sqrt T ≠ 0 := (Real.sqrt_pos.2 hT).ne'
        field_simp [hT.ne',hz]
        nlinarith only [hsq]
      rw [hs]
      exact mul_le_mul_of_nonneg_left (phi_bounded _).2 (by positivity)
  have H := (hfac.mul hΦ).add hsmall
  rw [mul_one,add_zero] at H
  apply H.congr'
  filter_upwards [htpos] with T hT
  unfold maxExpFormula
  field_simp [hT.ne']
  <;> ring

theorem exp_layercake {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (M : Ω → ℝ)
    (hm : AEMeasurable M μ) (h0 : 0 ≤ᵐ[μ] M) :
    (∫⁻ w, ENNReal.ofReal (Real.exp (M w)) ∂μ) =
      1 + ∫⁻ t in Ioi (0:ℝ), μ {w | t < M w} * ENNReal.ofReal (Real.exp t) := by
  have hl := lintegral_comp_eq_lintegral_meas_lt_mul μ h0 hm
    (g := Real.exp) (fun t _ ↦ Real.continuous_exp.intervalIntegrable 0 t)
    (Filter.Eventually.of_forall fun t ↦ (Real.exp_pos t).le)
  simp only [integral_exp, Real.exp_zero] at hl
  have hp : (fun w ↦ ENNReal.ofReal (Real.exp (M w))) =ᵐ[μ]
      fun w ↦ 1 + ENNReal.ofReal (Real.exp (M w)-1) := by
    filter_upwards [h0] with w hw
    have he : 0 ≤ Real.exp (M w)-1 := sub_nonneg.mpr (Real.one_le_exp hw)
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one he]
    congr 1
    ring
  rw [lintegral_congr_ae hp, lintegral_add_left measurable_const, lintegral_const, measure_univ,
    mul_one, hl]
end CubeBrownian
#print axioms CubeBrownian.maxExpFormula_div_tendsto_one
#print axioms CubeBrownian.exp_layercake
