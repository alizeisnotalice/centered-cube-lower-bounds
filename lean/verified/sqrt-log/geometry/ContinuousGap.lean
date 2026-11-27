import Continuous
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open Set MeasureTheory intervalIntegral

namespace CenteredCube.RudinDensity

theorem Rfun_abs (τ : ℝ) : Rfun |τ| = Rfun τ := by
  unfold Rfun
  apply intervalIntegral.integral_congr
  intro y _
  change Real.cos (2 * Real.pi * |τ| * y) = Real.cos (2 * Real.pi * τ * y)
  rcases le_total 0 τ with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_nonpos h, show 2 * Real.pi * -τ * y = -(2 * Real.pi * τ * y) by ring,
      Real.cos_neg]

theorem Rfun_sinc_pos {τ : ℝ} (hτ : 0 < τ) :
    Rfun τ = (Real.sin (Real.pi * τ) / (Real.pi * τ)) *
      Real.cos (3 * Real.pi * τ) := by
  have hc : 2 * Real.pi * τ ≠ 0 := by positivity
  let F : ℝ → ℝ := fun y => Real.sin ((2 * Real.pi * τ) * y) / (2 * Real.pi * τ)
  have hF (y : ℝ) : HasDerivAt F (Real.cos (2 * Real.pi * τ * y)) y := by
    have h := ((((hasDerivAt_id y).const_mul (2 * Real.pi * τ)).sin).div_const (2 * Real.pi * τ))
    convert h using 1
    · rfl
    · simp only [id_eq, mul_one]
      field_simp
  have hf : Continuous fun y : ℝ => Real.cos (2 * Real.pi * τ * y) := by fun_prop
  unfold Rfun
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hF y) (hf.intervalIntegrable _ _)]
  dsimp [F]
  rw [← sub_div, Real.sin_sub_sin]
  have haa : (2 * Real.pi * τ * 2 + 2 * Real.pi * τ * 1) / 2 = 3 * Real.pi * τ := by ring
  have hbb : (2 * Real.pi * τ * 2 - 2 * Real.pi * τ * 1) / 2 = Real.pi * τ := by ring
  rw [haa, hbb]
  field_simp
  <;> ring

private theorem sin_div_mono_bounds {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y)
    (hy : y ≤ Real.pi) : Real.sin y / y ≤ Real.sin x / x := by
  have hypos := hx.trans_le hxy
  have hcoef : x / y ≤ 1 := (div_le_one hypos).2 hxy
  have ht : 0 ≤ x / y := by positivity
  have hconc : ConcaveOn ℝ (Icc 0 Real.pi) Real.sin :=
    strictConcaveOn_sin_Icc.concaveOn
  have hsen : (1 - x/y) • Real.sin (0 : ℝ) + (x/y) • Real.sin y ≤
      Real.sin ((1 - x/y) • (0 : ℝ) + (x/y) • y) :=
    hconc.2 ⟨le_rfl, Real.pi_pos.le⟩ ⟨hypos.le, hy⟩ (sub_nonneg.mpr hcoef) ht (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.sin_zero] at hsen
  have hxy' : x / y * y = x := div_mul_cancel₀ x hypos.ne'
  rw [hxy'] at hsen
  apply (le_div_iff₀ hx).2
  convert hsen using 1
  ring

theorem Rfun_uniform_lower (τ : ℝ) : -(3 / Real.pi) ≤ Rfun τ := by
  rw [← Rfun_abs τ]
  set w := |τ| with hw
  have hw0 : 0 ≤ w := abs_nonneg _
  rcases eq_or_lt_of_le hw0 with h0 | hwpos
  · rw [← h0]
    simp [Rfun]
    have : 0 ≤ (3 : ℝ) / Real.pi := by positivity
    linarith
  rw [Rfun_sinc_pos hwpos]
  have hp0 : 0 < Real.pi * w := by positivity
  rcases le_or_gt w 1 with hle | hgt
  · have hpi : Real.pi * w ≤ Real.pi := by
      simpa using mul_le_mul_of_nonneg_left hle Real.pi_pos.le
    have hn : 0 ≤ Real.sin (Real.pi * w) / (Real.pi * w) :=
      div_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hp0.le hpi) hp0.le
    rcases le_or_gt w (1/6) with hsmall | hlarge
    · have hc : 0 ≤ Real.cos (3 * Real.pi * w) := by
        refine Real.cos_nonneg_of_mem_Icc ⟨?_, ?_⟩
        · have hp := Real.pi_pos
          nlinarith only [show 0 ≤ 3*Real.pi*w by positivity, hp]
        · have hmul := mul_le_mul_of_nonneg_left hsmall
            (show 0 ≤ 3 * Real.pi by positivity)
          linarith
      exact (neg_nonpos.mpr (by positivity)).trans (mul_nonneg hn hc)
    · have hh := sin_div_mono_bounds (x := Real.pi/6) (y := Real.pi*w)
        (by positivity) (by nlinarith only [mul_le_mul_of_nonneg_left hlarge.le Real.pi_pos.le]) hpi
      rw [Real.sin_pi_div_six] at hh
      have hh' : Real.sin (Real.pi * w) / (Real.pi * w) ≤ 3 / Real.pi := by
        convert hh using 1
        field_simp
        <;> norm_num
      nlinarith only [mul_le_mul_of_nonneg_left (Real.neg_one_le_cos (3*Real.pi*w)) hn, hh']
  · have hb : |Real.sin (Real.pi*w) / (Real.pi*w) * Real.cos (3*Real.pi*w)| ≤ 1 / Real.pi := by
      rw [abs_mul, abs_div, abs_of_pos hp0]
      have h₁ := div_le_div_of_nonneg_right (Real.abs_sin_le_one (Real.pi*w)) hp0.le
      have hc := Real.abs_cos_le_one (3*Real.pi*w)
      have hh : Real.pi ≤ Real.pi*w := by
        simpa using mul_le_mul_of_nonneg_left hgt.le Real.pi_pos.le
      calc
        _ ≤ (1/(Real.pi*w))*1 := mul_le_mul h₁ hc (abs_nonneg _) (by positivity)
        _ ≤ _ := by simpa using one_div_le_one_div_of_le Real.pi_pos hh
    have h := (abs_le.mp hb).1
    have hc : (1 : ℝ)/Real.pi ≤ 3/Real.pi :=
      div_le_div_of_nonneg_right (by norm_num) Real.pi_pos.le
    exact (neg_le_neg hc).trans h

theorem Rfun_uniform_upper {τ : ℝ} (hτ : (1:ℝ)/8 ≤ |τ|) :
    Rfun τ ≤ Real.sin (Real.pi / 8) / (Real.pi / 8) := by
  rw [← Rfun_abs τ]
  set w := |τ| with hw
  have hwpos : 0 < w := by linarith
  have hp0 : 0 < Real.pi*w := by positivity
  have hpi8 : 0 < Real.pi/8 := by positivity
  rw [Rfun_sinc_pos hwpos]
  rcases le_or_gt w 1 with hle | hgt
  · have hpi : Real.pi * w ≤ Real.pi := by
      simpa using mul_le_mul_of_nonneg_left hle Real.pi_pos.le
    have hn : 0 ≤ Real.sin (Real.pi * w) / (Real.pi * w) :=
      div_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hp0.le hpi) hp0.le
    have hr := sin_div_mono_bounds hpi8
      (show Real.pi/8 ≤ Real.pi*w by
        nlinarith only [mul_le_mul_of_nonneg_left hτ Real.pi_pos.le]) hpi
    exact (mul_le_of_le_one_right hn (Real.cos_le_one _)).trans hr
  · have hA : |Real.sin (Real.pi*w) / (Real.pi*w) * Real.cos (3*Real.pi*w)| ≤ 1/Real.pi := by
      rw [abs_mul, abs_div, abs_of_pos hp0]
      have hp : Real.pi ≤ Real.pi * w := by
        simpa using mul_le_mul_of_nonneg_left hgt.le Real.pi_pos.le
      calc
        _ ≤ (1/(Real.pi*w))*1 := mul_le_mul
          (div_le_div_of_nonneg_right (Real.abs_sin_le_one _) hp0.le)
          (Real.abs_cos_le_one _) (abs_nonneg _) (by positivity)
        _ ≤ _ := by simpa using one_div_le_one_div_of_le Real.pi_pos hp
    have hB := Real.mul_le_sin hpi8.le (show Real.pi/8 ≤ Real.pi/2 by linarith [Real.pi_pos])
    have hC : 2 / Real.pi ≤ Real.sin (Real.pi/8) / (Real.pi/8) := (le_div_iff₀ hpi8).2 hB
    exact (abs_le.mp hA).2.trans
      ((div_le_div_of_nonneg_right (by norm_num : (1:ℝ) ≤ 2) Real.pi_pos.le).trans hC)

end CenteredCube.RudinDensity

#print axioms CenteredCube.RudinDensity.Rfun_uniform_lower
#print axioms CenteredCube.RudinDensity.Rfun_uniform_upper
