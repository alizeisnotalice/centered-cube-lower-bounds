import RateError
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
namespace CubeMD

private theorem normal_real_eq_integral (s : Set ℝ) :
    (gaussianReal 0 1).real s = ∫ x in s, gaussianPDFReal 0 1 x := by
  rw [Measure.real, gaussianReal_apply_eq_integral 0 (by norm_num : (1 : ℝ≥0) ≠ 0)]
  exact ENNReal.toReal_ofReal (integral_nonneg (gaussianPDFReal_nonneg _ _))

private theorem gaussian_Ico_bounds (a b : ℝ) (hab : a ≤ b) :
    (gaussianReal 0 1).real (Ico a b) ≤ (Real.sqrt (2 * Real.pi))⁻¹ * (b-a) ∧
    (0 ≤ a → b ≤ 3 → gaussianPDFReal 0 1 3 * (b-a) ≤ (gaussianReal 0 1).real (Ico a b)) := by
  let s := Ico a b
  have hfin : volume s < ∞ := by dsimp only [s]; rw [Real.volume_Ico]; exact ENNReal.ofReal_lt_top
  letI : IsFiniteMeasure ((volume : Measure ℝ).restrict s) := ⟨by simpa using hfin⟩
  have hD : Integrable (gaussianPDFReal 0 1) ((volume : Measure ℝ).restrict s) :=
    (integrable_gaussianPDFReal _ _).restrict
  let M := (Real.sqrt (2 * Real.pi))⁻¹
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  have hu (x : ℝ) : gaussianPDFReal 0 1 x ≤ M := by
    rw [gaussianPDFReal_def]
    simp only [NNReal.coe_one, mul_one, sub_zero]
    simpa only [M, mul_one] using
      mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg x)) (by norm_num))) hM
  rw [normal_real_eq_integral]
  constructor
  · have h := setIntegral_mono_on hD (integrable_const M) measurableSet_Ico (fun x _ ↦ hu x)
    simpa only [s, M, setIntegral_const, smul_eq_mul, Real.volume_real_Ico_of_le hab, mul_comm] using h
  · intro ha hb
    have hl (x : ℝ) (hx : x ∈ s) : gaussianPDFReal 0 1 3 ≤ gaussianPDFReal 0 1 x := by
      rw [gaussianPDFReal_def]
      simp only [NNReal.coe_one, mul_one, sub_zero]
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr _) hM
      have hx₀ := ha.trans hx.1
      have hx₃ := hx.2.le.trans hb
      nlinarith [mul_nonneg (sub_nonneg.mpr hx₃) (show 0 ≤ 3+x by linarith)]
    have h := setIntegral_mono_on (integrable_const (gaussianPDFReal 0 1 3)) hD measurableSet_Ico hl
    simpa only [s, M, setIntegral_const, smul_eq_mul, Real.volume_real_Ico_of_le hab, mul_comm] using h

private theorem iio_difference (ν : Measure ℝ) [IsFiniteMeasure ν] (a b : ℝ) (hab : a ≤ b) :
    ν.real (Ico a b) = ν.real (Iio b) - ν.real (Iio a) := by
  have he : Ico a b = Iio b \ Iio a := by ext x; simp [and_comm, not_lt]
  rw [he, measureReal_sdiff (Iio_subset_Iio hab) measurableSet_Iio]

theorem normal_comparison_half_open_strips (ν : Measure ℝ) [IsProbabilityMeasure ν] (δ : ℝ)
    (hCDF : ∀ x, |ν.real (Iio x) - (gaussianReal 0 1).real (Iio x)| ≤ δ)
    (a b : ℝ) (hab : a ≤ b) :
    ν.real (Ico a b) ≤ (Real.sqrt (2 * Real.pi))⁻¹ * (b-a) + 2*δ ∧
    (0 ≤ a → b ≤ 3 → gaussianPDFReal 0 1 3 * (b-a) - 2*δ ≤ ν.real (Ico a b)) := by
  have h := interval_error_of_cdf_errors _ _ _ _ _ (hCDF a) (hCDF b)
  rw [← iio_difference ν a b hab, ← iio_difference (gaussianReal 0 1) a b hab] at h
  obtain ⟨hl, hu⟩ := abs_le.mp h
  have gg := gaussian_Ico_bounds a b hab
  constructor
  · linarith [gg.1]
  · intro ha hb
    linarith [gg.2 ha hb]

theorem cdf_closed_to_open (ν τ : Measure ℝ) [IsFiniteMeasure ν] [IsFiniteMeasure τ] (δ : ℝ)
    (h : ∀ x, |ν.real (Iic x) - τ.real (Iic x)| ≤ δ) :
    ∀ x, |ν.real (Iio x) - τ.real (Iio x)| ≤ δ := by
  intro x
  obtain ⟨c, hc, hc_lt, hc_lim⟩ := exists_seq_strictMono_tendsto x
  have hc_union : (⋃ n, Iic (c n)) = Iio x := iUnion_Iic_eq_Iio_of_lt_of_tendsto hc_lt hc_lim
  have hlim (η : Measure ℝ) [IsFiniteMeasure η] :
      Tendsto (fun n ↦ η.real (Iic (c n))) atTop (𝓝 (η.real (Iio x))) := by
    have hT := tendsto_measure_iUnion_atTop (μ := η) (monotone_Iic.comp hc.monotone)
    change Tendsto (fun n ↦ η (Iic (c n))) atTop (𝓝 (η (⋃ n, Iic (c n)))) at hT
    rw [hc_union] at hT
    exact (ENNReal.tendsto_toReal (measure_ne_top η (Iio x))).comp hT
  have ht := ((hlim ν).sub (hlim τ)).abs
  exact le_of_tendsto ht (Filter.Eventually.of_forall (fun n ↦ h (c n)))

end CubeMD
#print axioms CubeMD.normal_comparison_half_open_strips
#print axioms CubeMD.cdf_closed_to_open
