import SqrtWindowPulse
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

namespace CenteredCubeSqrt
open MeasureTheory Set
open scoped Interval
set_option maxHeartbeats 1800000

theorem interval_left_ramp_energy {a e : ℝ} (he : 0<e) :
    (∫ x in a..a+e, ((x-a)/e)^2)=e/3 := by
  simp_rw [div_pow,div_eq_mul_inv]
  rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_comp_sub_right (f:=fun x : ℝ => x^2)]
  rw [sub_self,add_sub_cancel_left,integral_pow]
  norm_num
  field_simp

theorem interval_right_ramp_energy {d e : ℝ} (he : 0<e) :
    (∫ x in d-e..d, ((d-x)/e)^2)=e/3 := by
  simp_rw [show ∀ x : ℝ, ((d-x)/e)^2=((x-d)/e)^2 by intro x; ring]
  simp_rw [div_pow,div_eq_mul_inv]
  rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_comp_sub_right (f:=fun x : ℝ => x^2)]
  rw [show d-e-d= -e by ring,sub_self,integral_pow]
  norm_num
  field_simp

theorem pulseOverlap_zero_width (e s : ℝ) (he : 0<e) : pulseOverlap e s s s s 0=0 := by
  exact le_antisymm (by simpa using (pulseOverlap_bounded he (s:=s) (t:=s) (s':=s) (t':=s) (delta:=0) le_rfl).2)
    (pulseOverlap_bounded he (s:=s) (t:=s) (s':=s) (t':=s) (delta:=0) le_rfl).1

theorem pulseOverlap_self_exact_above_width {e s t : ℝ} (he : 0<e) (hst : e≤t-s) :
    pulseOverlap e s t s t 0=t-s-e/3 := by
  let a := s-e/2
  let b := s+e/2
  let c := t-e/2
  let d := t+e/2
  let f (x : ℝ) := (smoothedWindowPulse e s t x)^2
  have hab : a≤b := by dsimp [a,b]; linarith
  have hbc : b≤c := by dsimp [b,c]; linarith
  have hcd : c≤d := by dsimp [c,d]; linarith
  have hf : Continuous f := (smoothedWindowPulse_continuous e s t).pow 2
  have hfit : Integrable f := by
    apply hf.integrable_of_hasCompactSupport
    apply HasCompactSupport.intro' (K:=Icc a d) isCompact_Icc isClosed_Icc
    intro x hx
    have HH : x<a ∨ d<x := by simpa only [mem_Icc,not_and_or,not_le] using hx
    unfold f
    rw [smoothedWindowPulse_zero_of_outside he HH]
    norm_num
  have supp : ∀ x, x∉Icc a d → f x=0 := by
    intro x hx
    have HH : x<a ∨ d<x := by simpa only [mem_Icc,not_and_or,not_le] using hx
    unfold f
    rw [smoothedWindowPulse_zero_of_outside he HH]
    norm_num
  have w₁ : (∫ x in a..b, f x)=e/3 := by
    calc
      _ = ∫ x in a..b, ((x-a)/e)^2 := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le hab] at hx
        have xa : a≤x := hx.1
        have xb : x≤b := hx.2
        unfold f
        rw [smoothedWindowPulse_eq_overlap,min_eq_right (by dsimp [b] at xb; linarith),
          show max s (x-e/2)=s by exact max_eq_left (by dsimp [b] at xb; linarith),
          max_eq_left (by dsimp [a] at xa; linarith)]
        dsimp [a]
        ring
      _ = _ := by
        rw [show b=a+e by dsimp [a,b]; ring]
        exact interval_left_ramp_energy he
  have w₂ : (∫ x in b..c, f x)=c-b := by
    calc
      _ = ∫ _ : ℝ in b..c, (1:ℝ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le hbc] at hx
        have xb : b≤x := hx.1
        have xc : x≤c := hx.2
        unfold f
        rw [smoothedWindowPulse_eq_overlap,min_eq_right (by dsimp [c] at xc; linarith),
          show max s (x-e/2)=x-e/2 by exact max_eq_right (by dsimp [b] at xb; linarith),
          max_eq_left (by linarith)]
        rw [show x+e/2-(x-e/2)=e by ring,div_self he.ne']
        norm_num
      _ = _ := by simp
  have w₃ : (∫ x in c..d, f x)=e/3 := by
    calc
      _ = ∫ x in c..d, ((d-x)/e)^2 := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le hcd] at hx
        have xc : c≤x := hx.1
        have xd : x≤d := hx.2
        unfold f
        rw [smoothedWindowPulse_eq_overlap,min_eq_left (by dsimp [c] at xc; linarith),
          show max s (x-e/2)=x-e/2 by exact max_eq_right (by dsimp [c] at xc; linarith),
          max_eq_left (by dsimp [d] at xd; linarith)]
        dsimp [d]
        ring
      _ = _ := by
        rw [show c=d-e by dsimp [c,d]; ring]
        exact interval_right_ramp_energy he
  unfold pulseOverlap
  simp_rw [sub_zero,←sq]
  change (∫ x, f x)=_
  have E : (∫ x, f x)=∫ x in Icc a d, f x := by
    rw [←integral_indicator measurableSet_Icc]
    congr 1
    funext x
    by_cases hx : x∈Icc a d
    · rw [indicator_of_mem hx]
    · rw [indicator_of_notMem hx,supp x hx]
  rw [E,integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le ((hab.trans hbc).trans hcd)]
  rw [←intervalIntegral.integral_add_adjacent_intervals ((hf.intervalIntegrable a b).trans (hf.intervalIntegrable b c))
    (hf.intervalIntegrable c d),
    ←intervalIntegral.integral_add_adjacent_intervals (hf.intervalIntegrable a b) (hf.intervalIntegrable b c),
    w₁,w₂,w₃]
  dsimp [b,c]
  ring

#print axioms pulseOverlap_self_exact_above_width
end CenteredCubeSqrt
