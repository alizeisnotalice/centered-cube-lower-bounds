import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace CenteredCubeSqrt

open MeasureTheory Set
open scoped Convolution
open Classical

noncomputable def realIntervalIndicator (s t : ℝ) (x : ℝ) : ℝ :=
  (Icc s t).indicator (fun _=>1) x

noncomputable def boxWindowDensity (eps : ℝ) (x : ℝ) : ℝ :=
  (Icc (-eps/2) (eps/2)).indicator (fun _=>1/eps) x

/-- The paper's b_[s,t], defined by the literal real convolution. -/
noncomputable def smoothedWindowPulse (eps s t : ℝ) (x : ℝ) : ℝ :=
  (realIntervalIndicator s t ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] boxWindowDensity eps) x

theorem realIntervalIndicator_integrable (s t : ℝ) :
    Integrable (realIntervalIndicator s t) := by
  unfold realIntervalIndicator
  apply (integrable_indicator_iff measurableSet_Icc).2
  exact integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)

theorem boxWindowDensity_integrable (eps : ℝ) :
    Integrable (boxWindowDensity eps) := by
  unfold boxWindowDensity
  apply (integrable_indicator_iff measurableSet_Icc).2
  exact integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)

theorem smoothedWindowPulse_eq_overlap (eps s t x : ℝ) :
    smoothedWindowPulse eps s t x =
      max (min t (x+eps/2) - max s (x-eps/2)) 0 / eps := by
  unfold smoothedWindowPulse
  rw [MeasureTheory.convolution_def]
  change (∫ y : ℝ, realIntervalIndicator s t y*boxWindowDensity eps (x-y)) = _
  have e (y : ℝ) :
      realIntervalIndicator s t y*boxWindowDensity eps (x-y) =
        (Icc (max s (x-eps/2)) (min t (x+eps/2))).indicator (fun _=>1/eps) y := by
    have mem : y ∈ Icc (max s (x-eps/2)) (min t (x+eps/2)) ↔
      y ∈ Icc s t ∧ x-y ∈ Icc (-eps/2) (eps/2) := by
      simp only [mem_Icc,max_le_iff,le_min_iff]
      constructor <;> intro h
      · exact ⟨⟨h.1.1,h.2.1⟩,⟨by linarith [h.2.2],by linarith [h.1.2]⟩⟩
      · exact ⟨⟨h.1.1,by linarith [h.2.2]⟩,⟨h.1.2,by linarith [h.2.1]⟩⟩
    unfold realIntervalIndicator boxWindowDensity
    by_cases hy : y ∈ Icc s t <;> by_cases hz : x-y ∈ Icc (-eps/2) (eps/2) <;>
      simp [mem,hy,hz]
  simp_rw [e]
  rw [integral_indicator_const _ measurableSet_Icc, Real.volume_real_Icc, smul_eq_mul]
  simp [div_eq_mul_inv]

theorem smoothedWindowPulse_integral {eps s t : ℝ} (he : 0 < eps) (hst : s ≤ t) :
    (∫ x, smoothedWindowPulse eps s t x) = t-s := by
  unfold smoothedWindowPulse
  rw [MeasureTheory.integral_convolution _
      (realIntervalIndicator_integrable s t) (boxWindowDensity_integrable eps)]
  change (∫ x, realIntervalIndicator s t x) * (∫ x, boxWindowDensity eps x) = _
  unfold realIntervalIndicator boxWindowDensity
  rw [integral_indicator_const _ measurableSet_Icc, integral_indicator_const _ measurableSet_Icc,
    Real.volume_real_Icc_of_le hst,
    Real.volume_real_Icc_of_le (show -eps/2 ≤ eps/2 by linarith)]
  simp only [smul_eq_mul,mul_one]
  field_simp
  ring

theorem smoothedWindowPulse_bounds {eps s t x : ℝ} (he : 0 < eps) :
    0 ≤ smoothedWindowPulse eps s t x ∧ smoothedWindowPulse eps s t x ≤ 1 := by
  rw [smoothedWindowPulse_eq_overlap]
  refine ⟨div_nonneg (le_max_right _ _) he.le, (div_le_one he).2 ?_⟩
  apply max_le
  · have h1 := min_le_right t (x+eps/2)
    have h2 := le_max_right s (x-eps/2)
    linarith
  · exact he.le

theorem smoothedWindowPulse_zero_of_outside {eps s t x : ℝ} (_he : 0 < eps)
    (h : x < s-eps/2 ∨ t+eps/2 < x) :
    smoothedWindowPulse eps s t x = 0 := by
  rw [smoothedWindowPulse_eq_overlap, max_eq_right,zero_div]
  rcases h with h | h
  · have h1 := min_le_right t (x+eps/2)
    have h2 := le_max_left s (x-eps/2)
    linarith
  · have h1 := min_le_left t (x+eps/2)
    have h2 := le_max_right s (x-eps/2)
    linarith

/-- Exact physical-variable pullback giving the 1/(Kv) coefficient. -/
theorem scaled_window_pulse_inner {eps s t s' t' C : ℝ} (hC : 0 < C) :
    (∫ x, smoothedWindowPulse eps s t (C*x)*smoothedWindowPulse eps s' t' (C*x)) =
      (1/C)*(∫ x, smoothedWindowPulse eps s t x*smoothedWindowPulse eps s' t' x) := by
  rw [Measure.integral_comp_mul_left (fun x => smoothedWindowPulse eps s t x *
      smoothedWindowPulse eps s' t' x) C, abs_of_pos (inv_pos.mpr hC), smul_eq_mul, one_div]

theorem smoothedWindowPulse_continuous (eps s t : ℝ) :
    Continuous (smoothedWindowPulse eps s t) := by
  have e : smoothedWindowPulse eps s t = fun x => max (min t (x+eps/2)-max s (x-eps/2)) 0/eps :=
    funext (smoothedWindowPulse_eq_overlap eps s t)
  rw [e]
  fun_prop

theorem smoothedWindowPulse_compactSupport {eps s t : ℝ} (he : 0 < eps) :
    HasCompactSupport (smoothedWindowPulse eps s t) := by
  apply HasCompactSupport.intro' (K:=Icc (s-eps/2) (t+eps/2)) isCompact_Icc isClosed_Icc
  intro x hx
  exact smoothedWindowPulse_zero_of_outside he (by
    simp only [mem_Icc,not_and_or,not_le] at hx
    exact hx)

theorem smoothedWindowPulse_integrable {eps s t : ℝ} (he : 0 < eps) :
    Integrable (smoothedWindowPulse eps s t) :=
  (smoothedWindowPulse_continuous eps s t).integrable_of_hasCompactSupport
    (smoothedWindowPulse_compactSupport he)

/-- The overlap kernel of two real box-smoothed pulses. -/
noncomputable def pulseOverlap (eps s t s' t' delta : ℝ) : ℝ :=
  ∫ x, smoothedWindowPulse eps s t x * smoothedWindowPulse eps s' t' (x-delta)

theorem pulseOverlap_bounded {eps s t s' t' delta : ℝ} (he : 0 < eps) (hst : s ≤ t) :
    0 ≤ pulseOverlap eps s t s' t' delta ∧ pulseOverlap eps s t s' t' delta ≤ t-s := by
  unfold pulseOverlap
  have hbound (x : ℝ) :
      smoothedWindowPulse eps s t x * smoothedWindowPulse eps s' t' (x-delta) ≤
      smoothedWindowPulse eps s t x :=
    mul_le_of_le_one_right (smoothedWindowPulse_bounds he).1 (smoothedWindowPulse_bounds he).2
  have hnon (x : ℝ) :
      0 ≤ smoothedWindowPulse eps s t x * smoothedWindowPulse eps s' t' (x-delta) :=
    mul_nonneg (smoothedWindowPulse_bounds he).1 (smoothedWindowPulse_bounds he).1
  have hInt : Integrable (fun x => smoothedWindowPulse eps s t x * smoothedWindowPulse eps s' t' (x-delta)) := by
    apply (smoothedWindowPulse_integrable he (s:=s) (t:=t)).mono'
    · exact ((smoothedWindowPulse_continuous eps s t).mul
        ((smoothedWindowPulse_continuous eps s' t').comp (continuous_id.sub continuous_const))).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs,abs_of_nonneg (hnon x)]; exact hbound x
  exact ⟨integral_nonneg hnon,
    (integral_mono hInt (smoothedWindowPulse_integrable he) hbound).trans_eq
      (smoothedWindowPulse_integral he hst)⟩

/-- This converts physical center proximity to support of the overlap sum,
with a uniform deterministic cutoff (2T+ε). -/
theorem pulseOverlap_zero_far {eps T s t s' t' delta : ℝ} (he : 0 < eps)
    (hs : -T ≤ s) (ht : t ≤ T) (hs' : -T ≤ s') (ht' : t' ≤ T)
    (hfar : 2*T+eps < |delta|) :
    pulseOverlap eps s t s' t' delta = 0 := by
  unfold pulseOverlap
  have hzero (x : ℝ) : smoothedWindowPulse eps s t x * smoothedWindowPulse eps s' t' (x-delta) = 0 := by
    by_cases hx : x < s-eps/2 ∨ t+eps/2 < x
    · rw [smoothedWindowPulse_zero_of_outside he hx,zero_mul]
    · by_cases hx' : x-delta < s'-eps/2 ∨ t'+eps/2 < x-delta
      · rw [smoothedWindowPulse_zero_of_outside he hx',mul_zero]
      · exfalso
        have h1 : s-eps/2 ≤ x := le_of_not_gt (fun h => hx (.inl h))
        have h2 : x ≤ t+eps/2 := le_of_not_gt (fun h => hx (.inr h))
        have h3 : s'-eps/2 ≤ x-delta := le_of_not_gt (fun h => hx' (.inl h))
        have h4 : x-delta ≤ t'+eps/2 := le_of_not_gt (fun h => hx' (.inr h))
        exact (not_le_of_gt hfar) (abs_le.mpr ⟨by linarith,by linarith⟩)
  simp_rw [hzero,integral_zero]

#print axioms pulseOverlap_bounded
#print axioms pulseOverlap_zero_far

#print axioms smoothedWindowPulse_eq_overlap
#print axioms smoothedWindowPulse_integral
#print axioms smoothedWindowPulse_bounds
#print axioms smoothedWindowPulse_zero_of_outside
#print axioms scaled_window_pulse_inner

end CenteredCubeSqrt
