import SqrtMidpointQuantizer

namespace CenteredCubeSqrt
open MeasureTheory Set
open scoped Interval BigOperators

noncomputable def scaledMidpointError (B j : ℕ) (t : ℝ) : ℝ :=
  midpointError B (((j:ℝ)+t)/(B:ℝ))

theorem scaledMidpointError_cell_integral {B j : ℕ} (hj : j<B) (n : ℕ) :
    (∫ x in (0:ℝ)..1, (scaledMidpointError B j x)^n) =
      (((-1:ℝ)/(B:ℝ))^n+(1/(B:ℝ))^n)*((1/2)^(n+1)/(n+1)) := by
  let F (x : ℝ) := (scaledMidpointError B j x)^n
  let A (x : ℝ) := ((-1/(B:ℝ))^n)*x^n
  let C (x : ℝ) := ((1/(B:ℝ))^n)*(1-x)^n
  have hA : Continuous A := by unfold A; fun_prop
  have hC : Continuous C := by unfold C; fun_prop
  have eA : EqOn F A (Ioo (0:ℝ) (1/2)) := by
    intro t h
    have h0 : t∈Icc (0:ℝ) 1 := ⟨h.1.le,by linarith [h.2]⟩
    unfold F A scaledMidpointError
    rw [midpointError_in_cell hj h0,ite_eq_left h.2,show -t/(B:ℝ)=(-1/(B:ℝ))*t by ring,mul_pow]
  have eC : EqOn F C (Ioo (1/2:ℝ) 1) := by
    intro t h
    have h0 : t∈Icc (0:ℝ) 1 := ⟨by linarith [h.1],h.2.le⟩
    unfold F C scaledMidpointError
    rw [midpointError_in_cell hj h0,ite_eq_right h.1.not_gt,show (1-t)/(B:ℝ)=(1/(B:ℝ))*(1-t) by ring,mul_pow]
  have ai : IntervalIntegrable F volume 0 (1/2) :=
    (intervalIntegrable_congr_uIoo (by rw [uIoo_of_le (show (0:ℝ)≤1/2 by norm_num)]; exact eA)).2
      (hA.intervalIntegrable _ _)
  have ci : IntervalIntegrable F volume (1/2) 1 :=
    (intervalIntegrable_congr_uIoo (by rw [uIoo_of_le (show (1/2:ℝ)≤1 by norm_num)]; exact eC)).2
      (hC.intervalIntegrable _ _)
  change (∫ x in (0:ℝ)..1, F x) = _
  rw [←intervalIntegral.integral_add_adjacent_intervals ai ci,
    intervalIntegral.integral_congr_Ioo_of_le (by norm_num) eA,
    intervalIntegral.integral_congr_Ioo_of_le (by norm_num) eC]
  unfold A C
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul]
  have hp : (∫ x in (0:ℝ)..(1/2), x^n)=((1/2)^(n+1)/(n+1)) := by rw [integral_pow]; simp
  rw [hp]
  have he : (∫ x in (1/2:ℝ)..1,(1-x)^n)= (∫ x in (0:ℝ)..(1/2),x^n) := by
    have h := intervalIntegral.integral_comp_sub_left (f:=fun x : ℝ => x^n) (a:=1/2) (b:=1) (1:ℝ)
    convert h using 1
    · norm_num
  rw [he,hp]
  ring

theorem scaledMidpointError_mean_zero {B j : ℕ} (hj : j<B) :
    (∫ x in (0:ℝ)..1, scaledMidpointError B j x) = 0 := by
  have h := scaledMidpointError_cell_integral hj 1
  simp only [pow_one] at h
  rw [h]
  ring

theorem scaledMidpointError_energy {B j : ℕ} (hj : j<B) :
    (∫ x in (0:ℝ)..1, (scaledMidpointError B j x)^2) = 1/(12*(B:ℝ)^2) := by
  rw [scaledMidpointError_cell_integral hj]
  norm_num
  ring

#print axioms scaledMidpointError_cell_integral
#print axioms scaledMidpointError_energy

end CenteredCubeSqrt
