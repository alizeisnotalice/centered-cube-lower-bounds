import SqrtRawRegularCorrelation
namespace CenteredCubeSqrt
open MeasureTheory Set
open scoped Interval BigOperators
set_option maxHeartbeats 1000000

theorem scaledMidpointError_subinterval_integrable {B j : ℕ} (hj : j<B)
    {a b : ℝ} (ha : 0≤a) (hb : b≤1) (hab : a≤b) :
    IntervalIntegrable (scaledMidpointError B j) volume a b := by
  have H := scaledMidpointError_power_integrable hj 1
  simp only [pow_one] at H
  apply H.mono_set
  rw [uIcc_of_le hab,uIcc_of_le (by norm_num : (0:ℝ)≤1)]
  exact Icc_subset_Icc ha hb

theorem scaledMidpointError_prefix_left {B j : ℕ} (hj : j<B) {t : ℝ} (ht : 0≤t) (ht' : t≤1/2) :
    (∫ x in (0:ℝ)..t,scaledMidpointError B j x) = -t^2/(2*(B:ℝ)) := by
  have he : EqOn (scaledMidpointError B j) (fun x : ℝ => (-1/(B:ℝ))*x) (Ioo 0 t) := by
    intro x hx
    unfold scaledMidpointError
    rw [midpointError_in_cell hj ⟨hx.1.le,by linarith [hx.2]⟩,ite_eq_left (hx.2.trans_le ht')]
    ring
  rw [intervalIntegral.integral_congr_Ioo_of_le ht he,intervalIntegral.integral_const_mul,integral_id]
  simp
  ring

theorem scaledMidpointError_suffix_right {B j : ℕ} (hj : j<B) {t : ℝ} (ht : 1/2≤t) (ht' : t≤1) :
    (∫ x in t..(1:ℝ),scaledMidpointError B j x) = (1-t)^2/(2*(B:ℝ)) := by
  have he : EqOn (scaledMidpointError B j) (fun x : ℝ => (1/(B:ℝ))*(1-x)) (Ioo t 1) := by
    intro x hx
    unfold scaledMidpointError
    rw [midpointError_in_cell hj ⟨by linarith [hx.1],hx.2.le⟩,ite_eq_right (not_lt_of_ge (ht.trans hx.1.le))]
    ring
  rw [intervalIntegral.integral_congr_Ioo_of_le ht' he,intervalIntegral.integral_const_mul]
  have h := intervalIntegral.integral_comp_sub_left (f:=fun x : ℝ => x) (a:=t) (b:=1) (1:ℝ)
  change (∫ x in t..(1:ℝ),1-x)=(∫ x in 1-1..1-t,x) at h
  rw [h,sub_self,integral_id]
  simp
  ring

theorem scaledMidpointError_prefix_right {B j : ℕ} (hj : j<B) {t : ℝ} (ht : 1/2≤t) (ht' : t≤1) :
    (∫ x in (0:ℝ)..t,scaledMidpointError B j x) = -(1-t)^2/(2*(B:ℝ)) := by
  have h := intervalIntegral.integral_add_adjacent_intervals
    (scaledMidpointError_subinterval_integrable hj (by norm_num) ht' (by linarith : 0≤t))
    (scaledMidpointError_subinterval_integrable hj (by linarith : 0≤t) (by norm_num) ht')
  rw [scaledMidpointError_mean_zero hj,scaledMidpointError_suffix_right hj ht ht'] at h
  rw [neg_div]
  exact eq_neg_of_add_eq_zero_left h

theorem scaledMidpointError_prefix_abs_bound {B j : ℕ} (hj : j<B) {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    - (1/(8*(B:ℝ)))≤(∫ x in (0:ℝ)..t,scaledMidpointError B j x) ∧
      (∫ x in (0:ℝ)..t,scaledMidpointError B j x)≤0 := by
  have hb : 0<(B:ℝ) := by exact_mod_cast (show 0<B by omega)
  have eq : (1:ℝ)/(8*(B:ℝ))=(1/4)/(2*(B:ℝ)) := by ring
  change -(1/(8*(B:ℝ)))≤(∫ x in (0:ℝ)..t,scaledMidpointError B j x) ∧ _
  rcases le_total t (1/2) with h|h
  · rw [scaledMidpointError_prefix_left hj ht.1 h,eq,neg_div]
    have H : t^2≤(1/4:ℝ) := (pow_le_pow_left₀ ht.1 h 2).trans_eq (by norm_num)
    exact ⟨neg_le_neg (div_le_div_of_nonneg_right H (by positivity)),neg_nonpos.mpr (by positivity)⟩
  · rw [scaledMidpointError_prefix_right hj h ht.2,eq,neg_div]
    have H : (1-t)^2≤(1/4:ℝ) := (pow_le_pow_left₀ (by linarith [ht.2] : 0≤1-t)
      (show 1-t≤1/2 by linarith) 2).trans_eq (by norm_num)
    exact ⟨neg_le_neg (div_le_div_of_nonneg_right H (by positivity)),neg_nonpos.mpr (by positivity)⟩

#print axioms scaledMidpointError_prefix_abs_bound
end CenteredCubeSqrt
