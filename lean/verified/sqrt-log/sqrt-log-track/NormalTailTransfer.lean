import TiltTransfer
import GaussianStrip
import RateError

open MeasureTheory ProbabilityTheory Set
namespace CubeMD

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ}

theorem preimage_standardized_strip (X : Ω → ℝ) (q m sd : ℝ)
    (hq : 0 < q) (hsd : 0 < sd) (k : ℕ) :
    (fun x ↦ (X x - m) / sd) ⁻¹'
      Ico ((k : ℝ) * (1 / (q * sd))) (((k : ℝ) + 1) * (1 / (q * sd))) =
      X ⁻¹' saddleStrip m q k := by
  have he (j : ℝ) : j * (1 / (q * sd)) * sd = j / q := by
    field_simp [hq.ne', hsd.ne']
  ext x
  change ((k : ℝ) * (1 / (q * sd)) ≤ (X x - m) / sd ∧
    (X x - m) / sd < ((k : ℝ) + 1) * (1 / (q * sd))) ↔
    (m + (k : ℝ) / q ≤ X x ∧ X x < m + ((k : ℝ) + 1) / q)
  rw [le_div_iff₀ hsd, div_lt_iff₀ hsd, he, he]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

theorem tilted_tail_of_normal_cdf [IsProbabilityMeasure μ]
    (hX : Measurable X) (q m sd z δ : ℝ) (hq : 0 < q) (hsd : 0 < sd) (hz : 1 ≤ z)
    (ht : Integrable (fun x ↦ Real.exp (q * X x)) μ)
    (hLenL : 1 / (Real.sqrt 6 * z) ≤ 1 / (q * sd))
    (hLenU : 1 / (q * sd) ≤ 3 / z)
    (hErrL : 2 * δ ≤ gaussianPDFReal 0 1 3 / (2 * Real.sqrt 6 * z))
    (hErrU : 2 * δ ≤ 2 / z)
    (hCDF : ∀ x, |((μ.tilted (q * X ·)).map (fun w ↦ (X w - m) / sd)).real (Iic x)
      - (gaussianReal 0 1).real (Iic x)| ≤ δ) :
    Real.exp (-q * m + cgf X μ q - 1) * (gaussianPDFReal 0 1 3 / (2 * Real.sqrt 6 * z)) ≤
      μ.real (X ⁻¹' Ici m) ∧
    μ.real (X ⁻¹' Ici m) ≤ Real.exp (-q * m + cgf X μ q) *
      ((3 * (Real.sqrt (2 * Real.pi))⁻¹ + 2) / z) / (1 - Real.exp (-1)) := by
  let ν := μ.tilted (q * X ·)
  letI : IsProbabilityMeasure ν := isProbabilityMeasure_tilted ht
  let U : Ω → ℝ := fun w ↦ (X w - m) / sd
  have hU : Measurable U := (hX.sub_const m).div_const sd
  let ν' := ν.map U
  haveI : IsProbabilityMeasure ν' := by dsimp only [ν']; infer_instance
  let l : ℝ := 1 / (q * sd)
  have hl : 0 ≤ l := by dsimp only [l]; positivity
  have hz' : 0 < z := zero_lt_one.trans_le hz
  have hL3 : l ≤ 3 := hLenU.trans ((div_le_iff₀ hz').mpr (by linarith))
  let φ : ℝ := gaussianPDFReal 0 1 3
  let M : ℝ := (Real.sqrt (2 * Real.pi))⁻¹
  have hm (k : ℕ) :
      ν'.real (Ico ((k : ℝ) * l) (((k : ℝ) + 1) * l)) =
        ν.real (X ⁻¹' saddleStrip m q k) := by
    simp only [Measure.real, ν', Measure.map_apply hU measurableSet_Ico]
    exact congrArg (fun s ↦ (ν s).toReal) (preimage_standardized_strip X q m sd hq hsd k)
  have hOpen : ∀ x, |ν'.real (Iio x) - (gaussianReal 0 1).real (Iio x)| ≤ δ :=
    cdf_closed_to_open ν' _ δ hCDF
  have hLower : φ * l - 2 * δ ≤ ν.real (X ⁻¹' saddleStrip m q 0) := by
    have h := (normal_comparison_half_open_strips ν' δ hOpen 0 l hl).2 le_rfl hL3
    rw [← hm 0]
    simpa [φ] using h
  have hUpper (k : ℕ) : ν.real (X ⁻¹' saddleStrip m q k) ≤ M * l + 2 * δ := by
    have hp : (k : ℝ) * l ≤ ((k : ℝ) + 1) * l :=
      mul_le_mul_of_nonneg_right (by linarith) hl
    have hh := (normal_comparison_half_open_strips ν' δ hOpen _ _ hp).1
    rw [hm k, show ((k : ℝ) + 1) * l - (k : ℝ) * l = l by ring] at hh
    exact hh
  have hLbound : φ / (2 * Real.sqrt 6 * z) ≤ ν.real (X ⁻¹' saddleStrip m q 0) := by
    have hφ : 0 ≤ φ := gaussianPDFReal_nonneg _ _ _
    have hLen := mul_le_mul_of_nonneg_left hLenL hφ
    have heq : φ * (1 / (Real.sqrt 6 * z)) = 2 * (φ / (2 * Real.sqrt 6 * z)) := by ring
    change φ * (1 / (Real.sqrt 6 * z)) ≤ φ * l at hLen
    rw [heq] at hLen
    change 2 * δ ≤ φ / (2 * Real.sqrt 6 * z) at hErrL
    linarith only [hLen, hErrL, hLower]
  have hUbound (k : ℕ) : ν.real (X ⁻¹' saddleStrip m q k) ≤ (3 * M + 2) / z := by
    calc
      _ ≤ M * l + 2 * δ := hUpper k
      _ ≤ M * (3 / z) + 2 / z :=
        add_le_add (mul_le_mul_of_nonneg_left hLenU (by dsimp only [M]; positivity)) hErrU
      _ = _ := by ring
  exact tilted_tail_of_strip_masses hX q m _ _ hq ht hLbound hUbound

end CubeMD
#print axioms CubeMD.preimage_standardized_strip
#print axioms CubeMD.tilted_tail_of_normal_cdf
