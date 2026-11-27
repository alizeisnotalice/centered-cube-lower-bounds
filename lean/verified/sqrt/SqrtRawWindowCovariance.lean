import SqrtRawCorrelation
import SqrtPeriodL2

namespace CenteredCubeSqrt
open MeasureTheory Set
open scoped Interval
set_option maxHeartbeats 1500000

theorem raw_primitive_two_shift_integral {B K : ℕ} [NeZero K] (f : ZMod K → Fin B)
    (a b : ℝ) :
    (∫ x in (0:ℝ)..1, actualRawPrimitive f (x+a)*actualRawPrimitive f (x+b)) =
      rawCorrelation f ((K:ℝ)*(b-a)) := by
  let P := actualRawPrimitive f
  let G (x : ℝ) := P x*P (x+(b-a))
  have e : (fun x => P (x+a)*P (x+b)) = fun x => G (x+a) := by
    funext x
    unfold G
    rw [show x+a+(b-a)=x+b by ring]
  have hP : Function.Periodic P 1 := actualRawPrimitive_periodic f
  have hG : Function.Periodic G 1 := by
    intro x
    unfold G
    rw [hP x,show x+1+(b-a)=x+(b-a)+1 by ring,hP (x+(b-a))]
  change (∫ x in (0:ℝ)..1, P (x+a)*P (x+b)) = _
  rw [e,intervalIntegral.integral_comp_add_right,zero_add,add_comm (1:ℝ),hG.intervalIntegral_add_eq a 0,zero_add]
  unfold rawCorrelation G P
  have hK : (K:ℝ)≠0 := by exact_mod_cast NeZero.ne K
  congr 1
  funext x
  rw [mul_div_cancel_left₀ _ hK]

theorem rawCorrelation_even {B K : ℕ} [NeZero K] (f : ZMod K → Fin B) (z : ℝ) :
    rawCorrelation f (-z)=rawCorrelation f z := by
  have hk : (K:ℝ)≠0 := by exact_mod_cast NeZero.ne K
  have a := raw_primitive_two_shift_integral f 0 (z/(K:ℝ))
  have b := raw_primitive_two_shift_integral f (z/(K:ℝ)) 0
  rw [sub_zero,mul_div_cancel₀ _ hk] at a
  rw [zero_sub,mul_neg,mul_div_cancel₀ _ hk] at b
  simp_rw [add_zero] at a b
  rw [←a,←b]
  simp only [mul_comm]

theorem rawWindow_covariance_from_correlation {B K : ℕ} [NeZero K] (f : ZMod K → Fin B)
    (L J : ℝ) :
    periodInner (actualRawWindow f L) (actualRawWindow f J) =
    2*rawCorrelation f ((K:ℝ)*(J-L)/2)-2*rawCorrelation f ((K:ℝ)*(J+L)/2) := by
  let P := actualRawPrimitive f
  have i (a b : ℝ) : IntervalIntegrable (fun x => P (x+a)*P (x+b)) volume 0 1 := by
    have hf := actualRawPrimitive_mul_intervalIntegrable f (b-a) (0+a) (1+a)
    have h := hf.comp_add_right a
    have e : (fun x => P (x+a)*P (x+a+(b-a))) = (fun x => P (x+a)*P (x+b)) := by
      funext x
      rw [show x+a+(b-a)=x+b by ring]
    rw [e,add_sub_cancel_right,add_sub_cancel_right] at h
    exact h
  unfold periodInner actualRawWindow
  change (∫ x in (0:ℝ)..1, (P (x+L/2)-P (x-L/2))*(P (x+J/2)-P (x-J/2))) = _
  have e (x : ℝ) : (P (x+L/2)-P (x-L/2))*(P (x+J/2)-P (x-J/2)) =
    (P (x+L/2)*P (x+J/2)-P (x+L/2)*P (x+ -(J/2)))-
      (P (x+ -(L/2))*P (x+J/2)-P (x+ -(L/2))*P (x+ -(J/2))) := by simp only [sub_eq_add_neg]; ring
  simp_rw [e]
  rw [intervalIntegral.integral_sub ((i _ _).sub (i _ _)) ((i _ _).sub (i _ _)),
    intervalIntegral.integral_sub (i _ _) (i _ _),intervalIntegral.integral_sub (i _ _) (i _ _),
    raw_primitive_two_shift_integral,raw_primitive_two_shift_integral,
    raw_primitive_two_shift_integral,raw_primitive_two_shift_integral]
  rw [show (K:ℝ)*(J/2-L/2)=(K:ℝ)*(J-L)/2 by ring,
    show (K:ℝ)*(-(J/2)-L/2)= -((K:ℝ)*(J+L)/2) by ring,
    show (K:ℝ)*(J/2- -(L/2))=(K:ℝ)*(J+L)/2 by ring,
    show (K:ℝ)*(-(J/2)- -(L/2))= -((K:ℝ)*(J-L)/2) by ring,
    rawCorrelation_even,rawCorrelation_even]
  ring

#print axioms rawWindow_covariance_from_correlation
end CenteredCubeSqrt
