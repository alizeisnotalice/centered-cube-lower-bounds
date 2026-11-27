import RetainedCountLimit
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

open Filter Finset
open scoped Topology
namespace CubeSqrtOverlap

theorem paper_deletion_fraction_tendsto_zero
    (K v deleted : ℕ → ℝ) (N : ℕ) (P : ℝ)
    (hP : 0 < P)
    (hK : ∀ᶠ n in atTop, 0 < K n) (hv : ∀ᶠ n in atTop, 1 ≤ v n)
    (hD0 : ∀ᶠ n in atTop, 0 ≤ deleted n)
    (hD : ∀ᶠ n in atTop,
      deleted n ≤ ((N:ℝ)+1)*(4*(v n)^2)*(2*v n/P+1))
    (hRate : Tendsto (fun n ↦ (v n)^2/K n) atTop (𝓝 0)) :
    Tendsto (fun n ↦ deleted n/(K n*v n/18)) atTop (𝓝 0) := by
  let C := 72*((N:ℝ)+1)*(2/P+1)
  have hL : Tendsto (fun n ↦ C*((v n)^2/K n)) atTop (𝓝 0) := by
    simpa only [mul_zero] using hRate.const_mul C
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hL ?_ ?_
  · filter_upwards [hK,hv,hD0] with n hk hv hd
    exact div_nonneg hd (by positivity)
  · filter_upwards [hK,hv,hD] with n hk hv hd
    have hv0 : 0 < v n := zero_lt_one.trans_le hv
    have hV : 0 < K n*v n/18 := by positivity
    have hA : 2*v n/P+1 ≤ (2/P+1)*v n := by
      rw [add_mul,one_mul,div_mul_eq_mul_div]
      linarith only [hv]
    calc
      _ ≤ (((N:ℝ)+1)*(4*(v n)^2)*(2*v n/P+1))/(K n*v n/18) :=
        div_le_div_of_nonneg_right hd hV.le
      _ ≤ (((N:ℝ)+1)*(4*(v n)^2)*((2/P+1)*v n))/(K n*v n/18) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hA (by positivity)) hV.le
      _ = _ := by unfold C; field_simp [hk.ne',hv0.ne',hP.ne'] <;> ring

theorem paper_raw_endpoint_tendsto
    (K v : ℕ → ℝ) (T P : ℝ) (hP : 0 < P) (hT : 0 ≤ T)
    (hV : Tendsto (fun n ↦ K n*v n/18) atTop atTop) :
    Tendsto (fun n ↦ 10/9+((rawPacketCount (K n*v n/18) T P):ℝ)*(2*P/(K n*v n)))
      atTop (𝓝 (11/9)) := by
  have h := (raw_packet_ratio_limit (fun n ↦ K n*v n/18) T P hV hP hT).const_mul (P/9)
  have hL : (P/9)*(1/P) = 1/9 := by field_simp [hP.ne']
  rw [hL] at h
  have H := h.const_add (10/9:ℝ)
  norm_num at H ⊢
  apply H.congr'
  filter_upwards [hV.eventually_gt_atTop 0] with n hn
  have hD : K n*v n ≠ 0 := by
    intro he
    rw [he,zero_div] at hn
    exact (lt_irrefl 0) hn
  change 10/9 + (P/9)*(((rawPacketCount (K n*v n/18) T P):ℝ)/(K n*v n/18)) =
    10/9 + ((rawPacketCount (K n*v n/18) T P):ℝ)*(2*P/(K n*v n))
  field_simp [hD] <;> ring

theorem paper_scaled_deletions_tendsto
    (K v deleted : ℕ → ℝ) (P : ℝ)
    (hV : Tendsto (fun n ↦ K n*v n/18) atTop atTop)
    (hD : Tendsto (fun n ↦ deleted n/(K n*v n/18)) atTop (𝓝 0)) :
    Tendsto (fun n ↦ (2*P/(K n*v n))*deleted n) atTop (𝓝 0) := by
  have H := hD.const_mul (P/9)
  rw [mul_zero] at H
  apply H.congr'
  filter_upwards [hV.eventually_gt_atTop 0] with n hn
  have hD : K n*v n ≠ 0 := by
    intro he
    rw [he,zero_div] at hn
    exact (lt_irrefl 0) hn
  change (P/9)*(deleted n/(K n*v n/18)) = (2*P/(K n*v n))*deleted n
  field_simp [hD] <;> ring

end CubeSqrtOverlap
#print axioms CubeSqrtOverlap.paper_deletion_fraction_tendsto_zero
#print axioms CubeSqrtOverlap.paper_raw_endpoint_tendsto
#print axioms CubeSqrtOverlap.paper_scaled_deletions_tendsto
