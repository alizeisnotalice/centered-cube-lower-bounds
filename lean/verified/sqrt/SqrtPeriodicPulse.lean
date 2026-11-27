import SqrtWindowPulse
import SqrtLocalWindowArithmetic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

namespace CenteredCubeSqrt

open MeasureTheory Set
open scoped Interval

/-- Centered representative of x modulo 1, chosen in [-1/2,1/2). -/
noncomputable def centeredPeriodRep (x : ℝ) : ℝ := x - ⌊x+1/2⌋

theorem centeredPeriodRep_range (x : ℝ) :
    -(1/2:ℝ) ≤ centeredPeriodRep x ∧ centeredPeriodRep x < 1/2 := by
  have hl := Int.floor_le (x+1/2)
  have hu := Int.lt_floor_add_one (x+1/2)
  unfold centeredPeriodRep
  exact ⟨by linarith,by linarith⟩

theorem centeredPeriodRep_eq {x : ℝ} (h : -(1/2:ℝ) ≤ x ∧ x < 1/2) :
    centeredPeriodRep x = x := by
  have hf : ⌊x+1/2⌋ = (0:ℤ) := Int.floor_eq_iff.mpr ⟨by push_cast; linarith [h.1],
    by push_cast; linarith [h.2]⟩
  rw [centeredPeriodRep,hf,Int.cast_zero,sub_zero]

theorem centeredPeriodRep_int {x : ℝ} (z : ℤ) :
    centeredPeriodRep (x+z) = centeredPeriodRep x := by
  unfold centeredPeriodRep
  rw [show x+(z:ℝ)+1/2 = x+1/2+z by ring,Int.floor_add_intCast]
  push_cast
  ring

theorem centeredPeriodRep_eq_or_shift {x : ℝ} (hx : |x| ≤ 3/4) :
    centeredPeriodRep x=x ∨
      (centeredPeriodRep x=x-1 ∧ 1/2 ≤ x) ∨
      (centeredPeriodRep x=x+1 ∧ x < -(1/2:ℝ)) := by
  rcases abs_le.mp hx with ⟨hlo,hhi⟩
  by_cases h1 : 1/2 ≤ x
  · right
    left
    have hf : ⌊x+1/2⌋ = (1:ℤ) := Int.floor_eq_iff.mpr ⟨by push_cast; linarith,
      by push_cast; linarith⟩
    exact ⟨by rw [centeredPeriodRep,hf,Int.cast_one],h1⟩
  · by_cases h0 : -(1/2:ℝ) ≤ x
    · exact Or.inl (centeredPeriodRep_eq ⟨h0,lt_of_not_ge h1⟩)
    · right
      right
      have hf : ⌊x+1/2⌋ = (-1:ℤ) := Int.floor_eq_iff.mpr ⟨by push_cast; linarith,
        by push_cast; linarith⟩
      exact ⟨by rw [centeredPeriodRep,hf]; push_cast; ring,lt_of_not_ge h0⟩

/-- Periodic lift of one scaled smoothed pulse (up to a choice of boundary
representative at points where the pulse vanishes). -/
noncomputable def periodicWindowPulse (eps s t C x : ℝ) : ℝ :=
  smoothedWindowPulse eps s t (C * centeredPeriodRep x)

theorem periodicWindowPulse_periodic (eps s t C : ℝ) :
    Function.Periodic (periodicWindowPulse eps s t C) 1 := by
  intro x
  unfold periodicWindowPulse
  have h := centeredPeriodRep_int (x:=x) 1
  norm_num at h
  rw [h]

theorem scaled_pulse_nonzero_support {eps s t C x M : ℝ} (he : 0 < eps) (hC : 0 < C)
    (hs : -M ≤ s-eps/2) (ht : t+eps/2 ≤ M)
    (hp : smoothedWindowPulse eps s t (C*x) ≠ 0) :
    |x| ≤ M/C := by
  have h1 : s-eps/2 ≤ C*x := le_of_not_gt (fun h => hp (smoothedWindowPulse_zero_of_outside he (.inl h)))
  have h2 : C*x ≤ t+eps/2 := le_of_not_gt (fun h => hp (smoothedWindowPulse_zero_of_outside he (.inr h)))
  rw [abs_le]
  constructor
  · rw [← neg_div,div_le_iff₀ hC]
    linarith
  · apply (le_div_iff₀ hC).mpr
    linarith

/-- If the first pulse is in its support and the relative center is chosen
in the fundamental interval, the second pulse's wrapped copy agrees with
the ordinary real value. No hidden cross-cell alias contributes. -/
theorem wrapped_pulse_equals_linear_on_first_support {eps s t s' t' C M x d : ℝ}
    (he : 0 < eps) (hC : 0 < C) (hm : M/C < 1/4)
    (hs : -M ≤ s-eps/2) (ht : t+eps/2 ≤ M)
    (hs' : -M ≤ s'-eps/2) (ht' : t'+eps/2 ≤ M)
    (hx : smoothedWindowPulse eps s t (C*x) ≠ 0)
    (hd : |d| ≤ 1/2) :
    periodicWindowPulse eps s' t' C (x-d) = smoothedWindowPulse eps s' t' (C*(x-d)) := by
  have hxabs := scaled_pulse_nonzero_support he hC hs ht hx
  have hxd : |x-d| ≤ 3/4 :=
    (abs_sub _ _).trans (by linarith)
  unfold periodicWindowPulse
  rcases centeredPeriodRep_eq_or_shift hxd with h | ⟨h,hlo⟩ | ⟨h,hhi⟩
  · rw [h]
  · rw [h]
    have hl : smoothedWindowPulse eps s' t' (C*(x-d-1)) = 0 := by
      by_contra hn
      have h' := (abs_le.mp (scaled_pulse_nonzero_support he hC hs' ht' hn)).1
      have hh := (abs_le.mp hxd).2
      linarith
    have hr : smoothedWindowPulse eps s' t' (C*(x-d)) = 0 := by
      by_contra hn
      have h' := (abs_le.mp (scaled_pulse_nonzero_support he hC hs' ht' hn)).2
      linarith
    rw [hl,hr]
  · rw [h]
    have hl : smoothedWindowPulse eps s' t' (C*(x-d+1)) = 0 := by
      by_contra hn
      have h' := (abs_le.mp (scaled_pulse_nonzero_support he hC hs' ht' hn)).2
      have hh := (abs_le.mp hxd).1
      linarith
    have hr : smoothedWindowPulse eps s' t' (C*(x-d)) = 0 := by
      by_contra hn
      have h' := (abs_le.mp (scaled_pulse_nonzero_support he hC hs' ht' hn)).1
      linarith
    rw [hl,hr]

theorem periodic_pulse_equals_real_on_fundamental {eps s t C M x : ℝ}
    (he : 0 < eps) (hC : 0 < C) (hm : M/C < 1/4)
    (hs : -M ≤ s-eps/2) (ht : t+eps/2 ≤ M)
    (hx : x ∈ Icc (-(1/2:ℝ)) (1/2)) :
    periodicWindowPulse eps s t C x = smoothedWindowPulse eps s t (C*x) := by
  rcases hx.2.lt_or_eq with hlt | rfl
  · simp only [periodicWindowPulse,centeredPeriodRep_eq ⟨hx.1,hlt⟩]
  · have hr : centeredPeriodRep (1/2:ℝ)= -(1/2:ℝ) := by
      calc
        _ = centeredPeriodRep (-(1/2:ℝ)+(1:ℤ)) := congrArg centeredPeriodRep (by norm_num)
        _ = centeredPeriodRep (-(1/2:ℝ)) := centeredPeriodRep_int 1
        _ = _ := centeredPeriodRep_eq ⟨le_rfl,by norm_num⟩
    unfold periodicWindowPulse
    rw [hr]
    have hz (y : ℝ) (hy : |y|=1/2) : smoothedWindowPulse eps s t (C*y)=0 := by
      by_contra hn
      have hh := scaled_pulse_nonzero_support he hC hs ht hn
      linarith
    rw [hz _ (by norm_num),hz _ (by norm_num)]

/-- Exact cross-pulse integral over one physical period, with the only
potential wrap accounted for by the centered representative of the lag. -/
theorem periodic_pulse_overlap_integral {eps s t s' t' C M d : ℝ}
    (he : 0 < eps) (hC : 0 < C) (hm : M/C < 1/4)
    (hs : -M ≤ s-eps/2) (ht : t+eps/2 ≤ M)
    (hs' : -M ≤ s'-eps/2) (ht' : t'+eps/2 ≤ M)
    (hd : |d| ≤ 1/2) :
    (∫ x in (-(1/2:ℝ))..(1/2), periodicWindowPulse eps s t C x *
       periodicWindowPulse eps s' t' C (x-d)) =
      (1/C) * pulseOverlap eps s t s' t' (C*d) := by
  have hEq : EqOn
      (fun x => periodicWindowPulse eps s t C x * periodicWindowPulse eps s' t' C (x-d))
      (fun x => smoothedWindowPulse eps s t (C*x) * smoothedWindowPulse eps s' t' (C*(x-d)))
      [[-(1/2:ℝ),1/2]] := by
    intro x hx
    rw [uIcc_of_le (by norm_num)] at hx
    have e := periodic_pulse_equals_real_on_fundamental he hC hm hs ht hx
    change _ * _ = _ * _
    rw [e]
    by_cases hz : smoothedWindowPulse eps s t (C*x)=0
    · rw [hz,zero_mul,zero_mul]
    · rw [wrapped_pulse_equals_linear_on_first_support he hC hm hs ht hs' ht' hz hd]
  rw [intervalIntegral.integral_congr hEq]
  rw [intervalIntegral.integral_eq_integral_of_support_subset]
  · simp_rw [mul_sub]
    unfold pulseOverlap
    rw [Measure.integral_comp_mul_left
      (fun z => smoothedWindowPulse eps s t z*smoothedWindowPulse eps s' t' (z-C*d)) C,
      abs_of_pos (inv_pos.mpr hC),smul_eq_mul,one_div]
  · intro x hx
    have he' : smoothedWindowPulse eps s t (C*x) ≠ 0 := by
      intro h
      exact hx (by simp [h])
    have ha := abs_le.mp (scaled_pulse_nonzero_support he hC hs ht he')
    exact ⟨by linarith [ha.1],by linarith [ha.2]⟩

/-- Arbitrary physical centers, integral with normalized period-one
Lebesgue measure. Both periodization and the exact C⁻¹ factor are explicit. -/
theorem periodic_two_centers_overlap {eps s t s' t' C M a b : ℝ}
    (he : 0 < eps) (hC : 0 < C) (hm : M/C < 1/4)
    (hs : -M ≤ s-eps/2) (ht : t+eps/2 ≤ M)
    (hs' : -M ≤ s'-eps/2) (ht' : t'+eps/2 ≤ M) :
    (∫ x in (0:ℝ)..1, periodicWindowPulse eps s t C (x-a) *
      periodicWindowPulse eps s' t' C (x-b)) =
      (1/C) * pulseOverlap eps s t s' t' (C*centeredPeriodRep (b-a)) := by
  let d := centeredPeriodRep (b-a)
  let f := fun x => periodicWindowPulse eps s t C x * periodicWindowPulse eps s' t' C (x-d)
  have hp : Function.Periodic f 1 := by
    intro x
    unfold f
    rw [periodicWindowPulse_periodic, show x+1-d=(x-d)+1 by ring, periodicWindowPulse_periodic]
  have e (x : ℝ) : periodicWindowPulse eps s' t' C (x-b) =
      periodicWindowPulse eps s' t' C ((x-a)-d) := by
    have hshift : x-a-d = (x-b)+(⌊b-a+1/2⌋:ℤ) := by dsimp [d, centeredPeriodRep]; ring
    rw [hshift]
    simp only [periodicWindowPulse,centeredPeriodRep_int]
  simp_rw [e]
  change (∫ x in (0:ℝ)..1, f (x-a)) = _
  rw [intervalIntegral.integral_comp_sub_right _ a]
  have e' : (∫ x in 0-a..1-a, f x) = (∫ x in (-(1/2:ℝ))..(1/2), f x) := by
    have h := hp.intervalIntegral_add_eq (0-a) (-(1/2:ℝ))
    rw [show (0:ℝ)-a+1=1-a by ring,show -(1/2:ℝ)+1=1/2 by norm_num] at h
    exact h
  rw [e']
  have hrep := centeredPeriodRep_range (b-a)
  exact periodic_pulse_overlap_integral he hC hm hs ht hs' ht'
    (abs_le.mpr ⟨hrep.1,hrep.2.le⟩)

#print axioms periodic_pulse_overlap_integral
#print axioms periodic_two_centers_overlap

#print axioms centeredPeriodRep_int
#print axioms periodicWindowPulse_periodic
#print axioms wrapped_pulse_equals_linear_on_first_support

end CenteredCubeSqrt
