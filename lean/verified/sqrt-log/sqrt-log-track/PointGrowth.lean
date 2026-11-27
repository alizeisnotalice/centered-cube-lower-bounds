import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

open Filter Asymptotics
open scoped Topology Asymptotics
namespace CubeMD

/-- Any fixed fourth logarithmic power is eventually dominated by the
dimension, in a form useful simultaneously for the finite thresholds. -/
theorem eventually_log_fourth_budget (A : ℝ) (hA : 0 < A) :
    ∀ᶠ n : ℕ in atTop, A * (Real.log (n:ℝ) + 1)^4 ≤ (n:ℝ) := by
  have ho := isLittleO_log_rpow_rpow_atTop (s := 1) 4 (by norm_num)
  have h₀ := ho.bound (show 0 < 1/(16*A) by positivity)
  have hc : Tendsto (fun n : ℕ ↦ (n:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hl : Tendsto (fun n : ℕ ↦ Real.log (n:ℝ)) atTop atTop := Real.tendsto_log_atTop.comp hc
  filter_upwards [hc.eventually h₀, hl.eventually_ge_atTop 1] with n hh hlog
  have hlog0 : 0 ≤ Real.log (n:ℝ) := by linarith
  rw [show (4:ℝ) = ((4:ℕ):ℝ) by norm_num, Real.rpow_natCast, Real.rpow_one] at hh
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hlog0 _),
    abs_of_nonneg (Nat.cast_nonneg _)] at hh
  have h' : (Real.log (n:ℝ))^4 * (16*A) ≤ n := by
    apply (le_div_iff₀ (by positivity : 0 < 16*A)).mp
    simpa only [one_div, one_mul, mul_comm, div_eq_mul_inv] using hh
  calc
    _ ≤ A * (2*Real.log (n:ℝ))^4 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith : 0 ≤ Real.log (n:ℝ)+1) (by linarith) _) hA.le
    _ = (Real.log (n:ℝ))^4 * (16*A) := by ring
    _ ≤ _ := h'

/-- One explicit growth budget implies all the scale, moderate-deviation
and quadratic-event absorption side conditions. -/
theorem onepoint_conditions_from_power (n K u B c : ℝ)
    (hn : 0 < n) (hK : 0 < K) (hu : 1 ≤ u) (hB : 0 ≤ B)
    (hcenter : u = Real.sqrt n/(90*Real.pi*K))
    (hscale : (32 * (90 * Real.pi))^2 * u^8 ≤ n)
    (hwindow : 64 * u^8 ≤ n)
    (hmd : (576*B^3)^2*u^8 ≤ n)
    (hbad : 32*(B^2+1)^2*(1+|Real.log (2/c)|)*u^8 ≤ n) :
    32*u ≤ K ∧ (2*u)^6 ≤ n ∧
      72*B^3*(2*u)^3/Real.sqrt n ≤ 1 ∧
      u^2+Real.log (2/c) ≤ n/(32*(B^2+1)^2*u^4) := by
  have hu0 : 0 < u := by linarith
  have hp2 : 1 ≤ u^2 := by nlinarith [sq_nonneg (u-1)]
  have hp4 : 1 ≤ u^4 := by nlinarith [sq_nonneg (u^2-1)]
  have hp6 : u^6 ≤ u^8 := by
    nlinarith only [mul_le_mul_of_nonneg_right hp2 (show 0 ≤ u^6 by positivity)]
  have hp48 : u^4 ≤ u^8 := by
    nlinarith only [mul_le_mul_of_nonneg_right hp4 (show 0 ≤ u^4 by positivity)]
  have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.2 hn
  have hD : 0 < 90*Real.pi*K := by positivity
  constructor
  · have hs : (32*(90*Real.pi)*u^2)^2 ≤ n := by
      calc
        _ = (32*(90*Real.pi))^2*u^4 := by ring
        _ ≤ (32*(90*Real.pi))^2*u^8 :=
          mul_le_mul_of_nonneg_left hp48 (by positivity)
        _ ≤ n := hscale
    have hh : 32*(90*Real.pi)*u^2 ≤ Real.sqrt n := by
      apply le_of_sq_le_sq _ hsqrt.le
      rwa [Real.sq_sqrt hn.le]
    have he := (eq_div_iff hD.ne').mp hcenter
    rw [← he] at hh
    have pos : 0 < (90*Real.pi)*u := by positivity
    apply le_of_mul_le_mul_right _ pos
    nlinarith only [hh]
  constructor
  · calc
      _ = 64*u^6 := by ring
      _ ≤ 64*u^8 := mul_le_mul_of_nonneg_left hp6 (by norm_num)
      _ ≤ _ := hwindow
  constructor
  · apply (div_le_iff₀ hsqrt).2
    rw [one_mul]
    apply le_of_sq_le_sq _ hsqrt.le
    rw [Real.sq_sqrt hn.le]
    calc
      _ = (576*B^3)^2*u^6 := by ring
      _ ≤ (576*B^3)^2*u^8 := mul_le_mul_of_nonneg_left hp6 (by positivity)
      _ ≤ _ := hmd
  · apply (le_div_iff₀ (by positivity : 0 < 32*(B^2+1)^2*u^4)).2
    have hp24 : u^2 ≤ u^4 := by
      nlinarith only [mul_le_mul_of_nonneg_right hp2 (sq_nonneg u)]
    have he : u^2+Real.log (2/c) ≤ (1+|Real.log (2/c)|)*u^4 := by
      have h1 := mul_le_mul_of_nonneg_left hp4 (abs_nonneg (Real.log (2/c)))
      linarith only [hp24,h1,le_abs_self (Real.log (2/c))]
    calc
      _ ≤ ((1+|Real.log (2/c)|)*u^4)*(32*(B^2+1)^2*u^4) :=
        mul_le_mul_of_nonneg_right he (by positivity)
      _ = _ := by ring
      _ ≤ _ := hbad

end CubeMD
#print axioms CubeMD.eventually_log_fourth_budget
#print axioms CubeMD.onepoint_conditions_from_power
