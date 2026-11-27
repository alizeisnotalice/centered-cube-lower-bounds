import WeightedGridError
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
namespace CubeBrownian

theorem truncated_exp_layercake {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (U : Ω → ℝ) (hmU : Measurable U) (δ : ℝ) :
    (∫⁻ w in {w | δ < U w}, ENNReal.ofReal (Real.exp (U w)) ∂μ) =
    μ {w | δ < U w} * ENNReal.ofReal (Real.exp δ) +
      ∫⁻ t in Ioi (0:ℝ), μ {w | δ+t < U w} * ENNReal.ofReal (Real.exp (δ+t)) := by
  let S := {w | δ < U w}
  let ν := μ.restrict S
  let V := fun w ↦ U w-δ
  let f := fun t : ℝ ↦ Real.exp (δ+t)
  have hS : MeasurableSet S := measurableSet_lt measurable_const hmU
  have h0 : 0 ≤ᵐ[ν] V := (ae_restrict_mem hS).mono (fun _ h ↦ sub_nonneg.mpr h.le)
  have hI (t : ℝ) : (∫ s in 0..t, f s) = Real.exp (δ+t)-Real.exp δ := by
    simp only [f,Real.exp_add,intervalIntegral.integral_const_mul,integral_exp,Real.exp_zero]
    ring
  have hc : Continuous f := by dsimp [f]; fun_prop
  have H := lintegral_comp_eq_lintegral_meas_lt_mul ν h0 (hmU.sub measurable_const).aemeasurable
    (g := f) (fun t _ ↦ hc.intervalIntegrable 0 t) (Eventually.of_forall fun t ↦ (Real.exp_pos _).le)
  simp_rw [hI] at H
  have hfun : (fun w ↦ ENNReal.ofReal (Real.exp (U w))) =ᵐ[ν]
      fun w ↦ ENNReal.ofReal (Real.exp δ) + ENNReal.ofReal (Real.exp (δ+V w)-Real.exp δ) := by
    filter_upwards [ae_restrict_mem hS] with w hw
    have hw' : δ ≤ U w := hw.le
    have he : δ+V w = U w := by dsimp [V]; ring
    rw [he,← ENNReal.ofReal_add (Real.exp_pos _).le
      (sub_nonneg.mpr (Real.exp_le_exp.mpr hw'))]
    congr 1
    ring
  rw [lintegral_congr_ae hfun,lintegral_add_left measurable_const,lintegral_const,
    Measure.restrict_apply MeasurableSet.univ,univ_inter,mul_comm _ (μ S),H]
  congr 1
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have he : {w | t < V w} = {w | δ+t < U w} := by
    ext w
    simp only [mem_ofPred_eq,V]
    constructor <;> intro h <;> linarith only [h]
  rw [he, Measure.restrict_apply (measurableSet_lt measurable_const hmU)]
  have hsub : {w | δ+t < U w} ⊆ S := by
    intro w hw
    exact ((lt_add_of_pos_right δ ht).trans hw)
  rw [inter_eq_left.mpr hsub]

theorem weighted_modulus_exp_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (U : Ω → ℝ) (hmU : Measurable U)
    (C : ℝ≥0∞) (b δ : ℝ) (hb : 0 < b) (hδ : 8*b ≤ δ)
    (hTail : ∀ x, b < x → μ {w | x < U w} ≤
      C * ENNReal.ofReal (Real.exp (-((x-b)^2)/(4*b)))) :
    (∫⁻ w in {w | δ < U w}, ENNReal.ofReal (Real.exp (U w)) ∂μ) ≤
      2 * C * ENNReal.ofReal (Real.exp (δ-δ^2/(8*b))) := by
  let K : ℝ≥0∞ := C * ENNReal.ofReal (Real.exp (δ-δ^2/(8*b)))
  have hT (t : ℝ) (ht : 0 ≤ t) :
      μ {w | δ+t < U w} * ENNReal.ofReal (Real.exp (δ+t)) ≤
      K * ENNReal.ofReal (Real.exp (-t)) := by
    have hp : b < δ+t := by linarith only [hb,hδ,ht]
    have haux : (δ+t)^2 ≤ 2*((δ+t-b)^2) := by
      have hh : 4*b ≤ δ+t := by linarith only [hb,hδ,ht]
      have hqq : 0 ≤ (δ+t)*(δ+t-4*b) := mul_nonneg (by linarith only [hb,hδ,ht]) (sub_nonneg.mpr hh)
      nlinarith only [hqq,sq_nonneg b]
    have hs : δ^2/(8*b)+2*t ≤ (δ+t-b)^2/(4*b) := by
      apply (le_div_iff₀ (by positivity : 0 < 4*b)).2
      have hh := mul_nonneg (show 0 ≤ δ-8*b by linarith only [hδ]) ht
      have hh₂ : (δ^2/(8*b)+2*t)*(4*b) = δ^2/2+8*b*t := by field_simp; ring
      rw [hh₂]
      nlinarith only [haux,hh,sq_nonneg t]
    calc
      _ ≤ (C * ENNReal.ofReal (Real.exp (-((δ+t-b)^2)/(4*b)))) *
            ENNReal.ofReal (Real.exp (δ+t)) := mul_le_mul' (hTail _ hp) le_rfl
      _ = C * ENNReal.ofReal (Real.exp ((δ+t)-((δ+t-b)^2)/(4*b))) := by
        rw [mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
        congr 3
        ring
      _ ≤ _ := by
        dsimp only [K]
        rw [mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
        exact mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by linarith only [hs])))
  have h0 := hT 0 le_rfl
  simp only [add_zero,neg_zero,Real.exp_zero,ENNReal.ofReal_one,mul_one] at h0
  have hExp : (∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (Real.exp (-t))) = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal]
    · have he : (∫ x : ℝ in Ioi (0:ℝ), Real.exp (-x)) = 1 := by
        have h := integral_exp_mul_Ioi (by norm_num : (-1:ℝ)<0) 0
        simpa only [neg_one_mul,mul_zero,neg_zero,Real.exp_zero,neg_div_neg_eq,div_one] using h
      rw [he,ENNReal.ofReal_one]
    · change IntegrableOn (fun t : ℝ ↦ Real.exp (-t)) (Ioi 0)
      simpa only [neg_one_mul] using integrableOn_exp_mul_Ioi (by norm_num : (-1:ℝ)<0) 0
    · exact Eventually.of_forall fun t ↦ (Real.exp_pos _).le
  have hInt : (∫⁻ t in Ioi (0:ℝ), μ {w | δ+t < U w} * ENNReal.ofReal (Real.exp (δ+t))) ≤ K := by
    calc
      _ ≤ ∫⁻ t in Ioi (0:ℝ), K * ENNReal.ofReal (Real.exp (-t)) := by
        apply lintegral_mono_ae
        exact (ae_restrict_mem measurableSet_Ioi).mono (fun t ht ↦ hT t (le_of_lt ht))
      _ = _ := by rw [lintegral_const_mul _ (by fun_prop), hExp, mul_one]
  rw [truncated_exp_layercake μ U hmU δ]
  calc
    _ ≤ K+K := add_le_add h0 hInt
    _ = _ := by rw [← two_mul,mul_assoc]
end CubeBrownian
#print axioms CubeBrownian.weighted_modulus_exp_bound
