import SqrtMidpointCellIntegrals

namespace CenteredCubeSqrt
open MeasureTheory Set
open scoped Interval BigOperators

theorem scaledMidpointError_power_integrable {B j : ℕ} (hj : j<B) (n : ℕ) :
    IntervalIntegrable (fun x => (scaledMidpointError B j x)^n) volume 0 1 := by
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
  exact ai.trans ci

theorem midpointError_cell_power_integrable {B j : ℕ} (hj : j<B) (n : ℕ) :
    IntervalIntegrable (fun x => (midpointError B x)^n) volume ((j:ℝ)/B) (((j+1:ℕ):ℝ)/B) := by
  have hB : (B:ℝ) ≠ 0 := by exact_mod_cast (show B ≠ 0 by omega)
  let F (x : ℝ) := (scaledMidpointError B j x)^n
  have hh : IntervalIntegrable F volume 0 1 := scaledMidpointError_power_integrable hj n
  have h := (hh.comp_add_right (-(j:ℝ))).comp_mul_left (c:=(B:ℝ))
  have e : (fun x : ℝ => F ((B:ℝ)*x+ -(j:ℝ))) = fun x => (midpointError B x)^n := by
    funext x
    have he : ((j:ℝ)+((B:ℝ)*x+ -(j:ℝ)))/(B:ℝ)=x := by field_simp; ring
    dsimp only [F,scaledMidpointError]
    rw [he]
  rw [e,sub_neg_eq_add,zero_add,sub_neg_eq_add,add_comm (1:ℝ)] at h
  simpa only [Nat.cast_add,Nat.cast_one] using h

theorem midpointError_cell_power_integral {B j : ℕ} (hj : j<B) (n : ℕ) :
    (∫ x in (j:ℝ)/(B:ℝ)..((j+1:ℕ):ℝ)/(B:ℝ),(midpointError B x)^n) =
      (1/(B:ℝ))*(∫ x in (0:ℝ)..1,(scaledMidpointError B j x)^n) := by
  let c := (1:ℝ)/(B:ℝ)
  have hB : (B:ℝ) ≠ 0 := by exact_mod_cast (show B ≠ 0 by omega)
  have hc : c ≠ 0 := one_div_ne_zero hB
  have e (x : ℝ) : c*x+(j:ℝ)/(B:ℝ)=((j:ℝ)+x)/(B:ℝ) := by unfold c; ring
  have hi := intervalIntegral.smul_integral_comp_mul_add
    (fun x => (midpointError B x)^n) (a:=0) (b:=1) c ((j:ℝ)/(B:ℝ))
  simp_rw [e] at hi
  simpa only [add_zero,smul_eq_mul,Nat.cast_add,Nat.cast_one,scaledMidpointError,c] using hi.symm

theorem midpointError_period_power_integral {B : ℕ} (hB : 0<B) (n : ℕ) :
    (∫ x in (0:ℝ)..1,(midpointError B x)^n) =
      (((-1:ℝ)/(B:ℝ))^n+(1/(B:ℝ))^n)*((1/2)^(n+1)/(n+1)) := by
  let f (x : ℝ) := (midpointError B x)^n
  have hBr : (B:ℝ)≠0 := by exact_mod_cast hB.ne'
  have h := intervalIntegral.sum_integral_adjacent_intervals (f:=f)
    (a:=fun j : ℕ => (j:ℝ)/(B:ℝ)) (n:=B)
    (fun j hj => midpointError_cell_power_integrable hj n)
  rw [Nat.cast_zero,zero_div,div_self hBr] at h
  rw [←h]
  have e (k : ℕ) (hk : k∈Finset.range B) :
      (∫ x in (k:ℝ)/(B:ℝ)..((k+1:ℕ):ℝ)/(B:ℝ), f x) =
      (1/(B:ℝ))*((((-1:ℝ)/(B:ℝ))^n+(1/(B:ℝ))^n)*((1/2)^(n+1)/(n+1))) := by
    rw [show (∫ x in (k:ℝ)/(B:ℝ)..((k+1:ℕ):ℝ)/(B:ℝ),f x) =
      (1/(B:ℝ))*(∫ x in (0:ℝ)..1,(scaledMidpointError B k x)^n) from
      midpointError_cell_power_integral (Finset.mem_range.mp hk) n,
      scaledMidpointError_cell_integral (Finset.mem_range.mp hk)]
  rw [Finset.sum_congr rfl e,Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  field_simp

theorem midpointError_period_energy {B : ℕ} (hB : 0<B) :
    (∫ x in (0:ℝ)..1,(midpointError B x)^2)=1/(12*(B:ℝ)^2) := by
  rw [midpointError_period_power_integral hB]
  norm_num
  ring

#print axioms midpointError_period_power_integral
#print axioms midpointError_period_energy

end CenteredCubeSqrt
