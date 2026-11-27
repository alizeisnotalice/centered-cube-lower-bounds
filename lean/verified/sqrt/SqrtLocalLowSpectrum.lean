import SqrtPlateauPolynomial
import Variance
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

namespace CenteredCubeSqrt

open MeasureTheory
open scoped BigOperators Interval

noncomputable def lowSpectrumAmp (m : ℕ) : ℝ :=
  Real.sqrt (2*plateauSpectralCoeff (m+1)/3)

noncomputable def actualLowSpectrum (M : ℕ) (L x : ℝ) : ℝ :=
  ∑ m ∈ Finset.range M, lowSpectrumAmp m *
    Real.sin ((m+1)*Real.pi*L) * Real.cos ((m+1)*(2*Real.pi)*x)

theorem positive_inverse_square_sum (M : ℕ) :
    (∑ m ∈ Finset.range (M+1), 1/((m:ℝ)+1)^2) ≤ 2-1/((M:ℝ)+1) := by
  induction M with
  | zero => norm_num
  | succ M ih =>
    rw [Finset.sum_range_succ, Nat.cast_succ]
    let a : ℝ := (M:ℝ)+1
    have ha : 0 < a := by dsimp [a]; positivity
    have hb : 0 < a+1 := by linarith
    have hfrac : 1/(a+1)^2 ≤ 1/a-1/(a+1) := by
      have e : 1/a-1/(a+1) = 1/(a*(a+1)) := by
        field_simp
        ring
      rw [e]
      apply div_le_div_of_nonneg_left (by norm_num) (mul_pos ha hb)
      nlinarith
    change _ + (1/(a+1)^2) ≤ 2-1/(a+1)
    linarith

theorem lowSpectrumAmp_energy_bound (M : ℕ) :
    (∑ m ∈ Finset.range M, ((m:ℝ)+1)^2*(lowSpectrumAmp m)^2) ≤ 800/81 := by
  have hsum : (∑ m ∈ Finset.range M, 1/((m:ℝ)+1)^2) ≤ 2 := by
    cases M with
    | zero => simp
    | succ M =>
      exact (positive_inverse_square_sum M).trans (sub_le_self _ (by positivity))
  have hpt (m : ℕ) :
      ((m:ℝ)+1)^2*(lowSpectrumAmp m)^2 ≤ (400/81)*(1/((m:ℝ)+1)^2) := by
    let a : ℝ := (m:ℝ)+1
    have ha : 0 < a := by dsimp [a]; positivity
    have hp : lowSpectrumAmp m < 20/(9*a^2) := plateauCoeff_amplitude a ha
    have hn : 0 ≤ lowSpectrumAmp m := Real.sqrt_nonneg _
    have hs := pow_le_pow_left₀ hn hp.le 2
    change a^2*_ ≤ _
    calc
      _ ≤ a^2*(20/(9*a^2))^2 := mul_le_mul_of_nonneg_left hs (by positivity)
      _ = (400/81)*(1/a^2) := by field_simp; ring
  calc
    _ ≤ ∑ m ∈ Finset.range M, (400/81)*(1/((m:ℝ)+1)^2) :=
      Finset.sum_le_sum (fun m _ => hpt m)
    _ = (400/81)*(∑ m ∈ Finset.range M, 1/((m:ℝ)+1)^2) := by rw [Finset.mul_sum]
    _ ≤ 800/81 := by linarith

/-- Exact paperlocal low-frequency L² increment bound, with constant
independent of the truncation M. -/
theorem actualLowSpectrum_difference_L2 (M : ℕ) (L J : ℝ) :
    (∫ x in (0:ℝ)..1, (actualLowSpectrum M L x-actualLowSpectrum M J x)^2) ≤
      ((400:ℝ)/81)*Real.pi^2*(L-J)^2 := by
  let a (m : ℕ) := lowSpectrumAmp m *
    (Real.sin ((m+1)*Real.pi*L)-Real.sin ((m+1)*Real.pi*J))
  have e (x : ℝ) : actualLowSpectrum M L x-actualLowSpectrum M J x =
      ∑ m ∈ Finset.range M, a m * Real.cos (((1+m:ℕ):ℝ)*(2*Real.pi)*x) := by
    unfold actualLowSpectrum
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro m _
    simp only [a, Nat.cast_add, Nat.cast_one, add_comm (1:ℝ)]
    ring
  simp_rw [e]
  rw [CenteredCube.RudinDensity.integral_cos_series_sq (M:=1) (by decide) a]
  have bound (m : ℕ) :
      (a m)^2 ≤ ((m:ℝ)+1)^2*(lowSpectrumAmp m)^2*(Real.pi^2*(L-J)^2) := by
    have h := Real.abs_sin_sub_sin_le (((m:ℝ)+1)*Real.pi*L) (((m:ℝ)+1)*Real.pi*J)
    have hr : (((m:ℝ)+1)*Real.pi*L)-(((m:ℝ)+1)*Real.pi*J) =
        (((m:ℝ)+1)*Real.pi)*(L-J) := by ring
    rw [hr,abs_mul, abs_of_nonneg (by positivity : 0 ≤ ((m:ℝ)+1)*Real.pi)] at h
    have he := pow_le_pow_left₀ (abs_nonneg _) h 2
    rw [sq_abs, mul_pow, mul_pow, sq_abs] at he
    unfold a
    rw [mul_pow]
    have hineq := mul_le_mul_of_nonneg_left he (sq_nonneg (lowSpectrumAmp m))
    nlinarith
  have henergy := lowSpectrumAmp_energy_bound M
  calc
    _ ≤ (1/2)*∑ m ∈ Finset.range M,
        (((m:ℝ)+1)^2*(lowSpectrumAmp m)^2)*(Real.pi^2*(L-J)^2) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Finset.sum_le_sum (fun m _ => bound m)
    _ = (1/2)*((∑ m ∈ Finset.range M, ((m:ℝ)+1)^2*(lowSpectrumAmp m)^2) *
        (Real.pi^2*(L-J)^2)) := by rw [Finset.sum_mul]
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_right henergy (by positivity : 0 ≤ Real.pi^2*(L-J)^2)
      nlinarith

#print axioms actualLowSpectrum_difference_L2

end CenteredCubeSqrt
