import SqrtActualAtomDiscrepancy
import SqrtActualDensityWindow

namespace CenteredCubeSqrt

open MeasureTheory
open scoped BigOperators Interval

theorem inverse_square_sum_le_two (M : ℕ) :
    (∑ m ∈ Finset.range M, 1/((m:ℝ)+1)^2) ≤ 2 := by
  cases M with
  | zero => simp
  | succ M => exact (positive_inverse_square_sum M).trans (sub_le_self _ (by positivity))

theorem actualLowSpectrum_continuous (M : ℕ) (L : ℝ) :
    Continuous (actualLowSpectrum M L) := by
  unfold actualLowSpectrum
  fun_prop

theorem actualLowSpectrum_abs_le {M : ℕ} (L x : ℝ) :
    |actualLowSpectrum M L x| ≤ 40/9 := by
  unfold actualLowSpectrum
  have e (m : ℕ) :
      |lowSpectrumAmp m * Real.sin (((m:ℝ)+1)*Real.pi*L) *
        Real.cos (((m:ℝ)+1)*(2*Real.pi)*x)| ≤ lowSpectrumAmp m := by
    have hn : 0 ≤ lowSpectrumAmp m := Real.sqrt_nonneg _
    rw [abs_mul,abs_mul,abs_of_nonneg hn]
    calc
      _ ≤ lowSpectrumAmp m * |Real.sin (((m:ℝ)+1)*Real.pi*L)| :=
        mul_le_of_le_one_right (by positivity) (Real.abs_cos_le_one _)
      _ ≤ _ := mul_le_of_le_one_right hn (Real.abs_sin_le_one _)
  calc
    _ ≤ ∑ m ∈ Finset.range M, |lowSpectrumAmp m * Real.sin (((m:ℝ)+1)*Real.pi*L) *
        Real.cos (((m:ℝ)+1)*(2*Real.pi)*x)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ m ∈ Finset.range M, (20/9)*(1/((m:ℝ)+1)^2) := by
      apply Finset.sum_le_sum
      intro m _
      have ha := plateauCoeff_amplitude ((m:ℝ)+1) (by positivity)
      have hrewrite : (20:ℝ)/(9*((m:ℝ)+1)^2) = (20/9)*(1/((m:ℝ)+1)^2) := by
        field_simp
      rw [← hrewrite]
      exact (e m).trans ha.le
    _ = (20/9)*(∑ m ∈ Finset.range M, 1/((m:ℝ)+1)^2) := by rw [Finset.mul_sum]
    _ ≤ 40/9 := by linarith [inverse_square_sum_le_two M]

theorem box_width_small_for_local_design {B K : ℕ} {eps v : ℝ}
    (hK : 0<K) (hB : 0<B) (hv : 0<v) (_he : 0<eps) (he4 : eps≤1/4)
    (hBv : (B:ℝ)≤2*v) :
    eps/((K:ℝ)*v) < 1/((B:ℝ)*K) := by
  have hb : 0 < (B:ℝ) := by exact_mod_cast hB
  have hk : 0 < (K:ℝ) := by exact_mod_cast hK
  apply (div_lt_div_iff₀ (mul_pos hk hv) (mul_pos hb hk)).mpr
  have heB : eps*(B:ℝ) ≤ v/2 := by
    have e1 := mul_le_mul_of_nonneg_right he4 hb.le
    linarith
  have := mul_lt_mul_of_pos_right (show eps*(B:ℝ)<v by linarith) hk
  nlinarith

/-- Exact actual atom plus low-spectrum window term bounded by 7, without
using the paper's sorting or asymptotic machinery. -/
theorem actual_compensated_window_abs_le_seven {B K : ℕ} [NeZero K]
    (f : ZMod K → Fin B) (M : ℕ) (hB : 0<B) (hK : 2≤K)
    {delta L : ℝ} (hδ0 : 0<delta) (hδ : delta <1/((B:ℝ)*K)) (x : ℝ) :
    |actualAtomicWindow f delta L x+actualLowSpectrum M L x| ≤ 7 := by
  apply (abs_add_le _ _).trans
  linarith [actualAtomicWindow_abs_le_two (L:=L) hB hK f hδ0 hδ x, actualLowSpectrum_abs_le (M:=M) L x]

/-- Exact denominator perturbation controlled by the scaled time. -/
theorem localLength_inverse_difference_bound {L0 C t : ℝ} (hC : 0<C)
    (h0 : 1≤L0) (hT : 1≤localLength L0 C t) :
    |1/localLength L0 C t - 1/L0| ≤ 2*|t|/C := by
  have hp : 0<L0 := by linarith
  have hq : 0<localLength L0 C t := by linarith
  have e : 1/localLength L0 C t - 1/L0 =
      (-(2*t/C))/(localLength L0 C t*L0) := by
    have e0 : localLength L0 C t-L0=2*t/C := by unfold localLength; ring
    rw [← e0]
    field_simp [hp.ne',hq.ne']
    ring
  rw [e,abs_div,abs_of_pos (mul_pos hq hp),abs_neg,abs_div,abs_of_pos hC,abs_mul,
    abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  have hden : 1≤localLength L0 C t*L0 := by
    exact (le_mul_of_one_le_right (by linarith) h0).trans' hT
  exact div_le_self (by positivity) hden

#print axioms actual_compensated_window_abs_le_seven
#print axioms localLength_inverse_difference_bound

end CenteredCubeSqrt
