import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace CenteredCubeSqrt

noncomputable def tentConvPoly (b x : ℝ) : ℝ :=
  if |x| ≤ b then 2*b^3/3 - b*|x|^2 + |x|^3/2
  else if |x| ≤ 2*b then (2*b-|x|)^3/6 else 0

noncomputable def plateauPoly (x : ℝ) : ℝ :=
  tentConvPoly (10/27) x + 3*tentConvPoly (1/9) x

theorem tentConvPoly_zero_of_support {b x : ℝ} (hb : 0 ≤ b) (hx : 2*b < |x|) :
    tentConvPoly b x = 0 := by
  have h1 : ¬ |x| ≤ b := by linarith
  have h2 : ¬ |x| ≤ 2*b := by linarith
  simp [tentConvPoly, h1, h2]

/-- No wrapped integer translate contributes to the positive-spectrum
plateau. This includes x=0 (indeed all x in [0,2/9]). -/
theorem plateauPoly_no_wrap {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) (2/9))
    {j : ℤ} (hj : j ≠ 0) : plateauPoly (x+(j:ℝ))=0 := by
  have h : 2*(10/27:ℝ) < |x+(j:ℝ)| := by
    rcases lt_or_gt_of_ne hj with hj | hj
    · have hj' : (j:ℝ) ≤ -1 := by exact_mod_cast (show j ≤ -1 by omega)
      rw [abs_of_nonpos (by linarith [hx.2])]
      linarith [hx.2]
    · have hj' : (1:ℝ) ≤ j := by exact_mod_cast (show 1 ≤ j by omega)
      rw [abs_of_nonneg (by linarith [hx.1])]
      linarith [hx.1]
  unfold plateauPoly
  rw [tentConvPoly_zero_of_support (by norm_num : (0:ℝ) ≤ 10/27) h,
    tentConvPoly_zero_of_support (by norm_num : (0:ℝ) ≤ 1/9) (by linarith)]
  ring

/-- Exact cubic cancellation; Fourier/convolution identification is separate. -/
theorem plateau_polynomial_exact {x : ℝ} (hx : x ∈ Set.Icc (1/9 : ℝ) (2/9)) :
    1 + (729/29)*(plateauPoly 0 - plateauPoly x) = (27/29)*(1+x)^2 := by
  have h0 : 0 ≤ x := by linarith [hx.1]
  have h1 : x ≤ 10/27 := by linarith [hx.2]
  have h2 : x ≤ 2*(1/9) := by linarith [hx.2]
  have hz1 : (0:ℝ) ≤ (10/27) := by norm_num
  have hz2 : (0:ℝ) ≤ (1/9) := by norm_num
  unfold plateauPoly tentConvPoly
  simp only [abs_zero, abs_of_nonneg h0, ite_eq_left h1, ite_eq_left h2, ite_eq_left hz1, ite_eq_left hz2]
  split
  · rename_i hs
    have he : x = 1/9 := le_antisymm hs hx.1
    rw [he]
    norm_num
  · ring

theorem plateau_normalized_bounds {L : ℝ} (hL : L ∈ Set.Icc (10/9 : ℝ) (11/9)) :
    (100/87 : ℝ) ≤ (27/29)*L^2 ∧ (27/29)*L^2 ≤ (121/87 : ℝ) := by
  have h0 : 0 ≤ L := by linarith [hL.1]
  constructor
  · have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 10/9) hL.1 2
    linarith
  · have h := pow_le_pow_left₀ h0 hL.2 2
    linarith

noncomputable def plateauSpectralCoeff (m : ℝ) : ℝ :=
  4*(729/29)*((Real.sin (Real.pi*m*(10/27))/(Real.pi*m))^4 +
    3*(Real.sin (Real.pi*m*(1/9))/(Real.pi*m))^4)

theorem plateauSpectralCoeff_nonneg (m : ℝ) : 0 ≤ plateauSpectralCoeff m := by
  unfold plateauSpectralCoeff
  positivity


theorem plateau_sine_fourth_bound (m : ℝ) (hm : 0 < m) (b : ℝ) :
    (Real.sin (Real.pi*m*b)/(Real.pi*m))^4 ≤ (1/(Real.pi*m))^4 := by
  have hmπ : 0 < Real.pi*m := mul_pos Real.pi_pos hm
  calc
    (Real.sin (Real.pi*m*b)/(Real.pi*m))^4
      = |Real.sin (Real.pi*m*b)/(Real.pi*m)|^4 := by
        rw [← abs_pow, abs_of_nonneg (by positivity)]
    _ ≤ (1/(Real.pi*m))^4 := by
      rw [abs_div, abs_of_pos hmπ]
      exact pow_le_pow_left₀ (by positivity)
        (div_le_div_of_nonneg_right (Real.abs_sin_le_one _) hmπ.le) 4

theorem plateauCoeff_majorant (m : ℝ) (hm : 0 < m) :
    plateauSpectralCoeff m ≤ 16*(729/29)/(Real.pi^4*m^4) := by
  have h1 := plateau_sine_fourth_bound m hm (10/27)
  have h2 := plateau_sine_fourth_bound m hm (1/9)
  unfold plateauSpectralCoeff
  simp only [div_pow, one_pow, mul_pow] at h1 h2 ⊢
  simp only [div_eq_mul_inv] at h1 h2 ⊢
  linarith

theorem plateauCoeff_amplitude (m : ℝ) (hm : 0 < m) :
    Real.sqrt (2*plateauSpectralCoeff m/3) < 20/(9*m^2) := by
  have hm2 : 0 < m^2 := sq_pos_of_pos hm
  have hm4 : 0 < m^4 := by positivity
  have hπ : 3 < Real.pi := Real.pi_gt_three
  have hπ4 : 81 < Real.pi^4 := by
    nlinarith [pow_lt_pow_left₀ hπ (show (0:ℝ) ≤ 3 by norm_num) (show 4 ≠ 0 by decide)]
  have hden : 0 < Real.pi^4*m^4 := by positivity
  have he := (le_div_iff₀ hden).mp (plateauCoeff_majorant m hm)
  have hc := plateauSpectralCoeff_nonneg m
  have hdenb := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hπ4.le hm4.le) hc
  have hM : 81*m^4*plateauSpectralCoeff m ≤ 16*(729/29) := by nlinarith
  have haux : 2*plateauSpectralCoeff m/3 < (20/(9*m^2))^2 := by
    rw [div_pow, mul_pow, ← pow_mul]
    apply (lt_div_iff₀ (by positivity)).2
    nlinarith
  have hsq := Real.sq_sqrt (show 0 ≤ 2*plateauSpectralCoeff m/3 by positivity)
  have hz : 0 ≤ Real.sqrt (2*plateauSpectralCoeff m/3) := Real.sqrt_nonneg _
  have hv : 0 < 20/(9*m^2) := by positivity
  by_contra! hn
  have := pow_le_pow_left₀ hv.le hn 2
  linarith

#print axioms plateauCoeff_majorant
#print axioms plateauCoeff_amplitude

#print axioms plateau_polynomial_exact
#print axioms plateauPoly_no_wrap
#print axioms plateau_normalized_bounds
#print axioms plateauSpectralCoeff_nonneg

end CenteredCubeSqrt
