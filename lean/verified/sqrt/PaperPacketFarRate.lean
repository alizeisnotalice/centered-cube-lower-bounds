import PaperPacketOverlapChoice
import PacketFarRates

namespace CenteredCubeSqrt
open Filter Finset CubeSqrtOverlap
open scoped Topology

theorem paper_raw_count_upper (V T P : ℝ) (hP : 0<P) (hT : 0≤T) (hRoom : T≤V) :
    (rawPacketCount V T P:ℝ)≤V/P+1 := by
  unfold rawPacketCount
  push_cast
  have hF := Nat.floor_le (div_nonneg (sub_nonneg.mpr hRoom) hP.le)
  have h := div_le_div_of_nonneg_right (show V-T≤V by linarith) hP.le
  linarith

theorem paper_all_integer_far_packet_rate {p : ℝ} (hp : 0<p) {d : ℕ→ℕ}
    (hd : ∀ᶠ n in atTop, 0<d n ∧
      16*Real.log n≤paperV p n (d n) ∧ paperV p n (d n)<144*Real.log n)
    {T P : ℝ} (hP : 0<P) (hT : 0≤T) :
    Tendsto (fun n =>
      let K := (paperPeriod (d n):ℝ)
      let v := paperV p n (d n)
      (rawPacketCount (K*v/18) T P:ℝ)*(actualPairPrefactor*Real.exp (-v/25)))
      atTop (𝓝 0) := by
  let K (n : ℕ) := (paperPeriod (d n):ℝ)
  let v (n : ℕ) := paperV p n (d n)
  let B (n : ℕ) : ℝ := rawPacketCount (K n*v n/18) T P
  have hcp : 0<paperCp p := by unfold paperCp; positivity
  have hv := paper_v_tendsto (v:=v) (hd.mono fun _ h => h.2.1)
  have hR : ∀ᶠ n in atTop, T≤K n*v n/18 := by
    have hK := paper_period_growth_of_choice hp d hd 0
    simp only [pow_zero,div_one] at hK
    have hK' := (hK.const_mul_atTop (by norm_num : (0:ℝ)<1/18)).eventually_ge_atTop T
    filter_upwards [hK',hv.eventually_ge_atTop 1,hK.eventually_ge_atTop 0] with n h1 h2 h3
    change T≤(1/18)*K n at h1
    have h3 : 0≤K n := h3
    linarith only [h1,mul_le_mul_of_nonneg_left h2 h3]
  have hB : ∀ᶠ n in atTop, B n≤(paperCp p/(18*P)+1)*Real.sqrt ((n:ℝ)*v n) := by
    filter_upwards [hR, hd, hv.eventually_ge_atTop 1, eventually_ge_atTop (1:ℕ)] with n hR hd hv hn
    have hs := paper_raw_count_upper (K n*v n/18) T P hP hT hR
    change B n≤_ at hs
    have hx : (1:ℝ)≤n := by exact_mod_cast hn
    have hU : 1≤Real.sqrt ((n:ℝ)*v n) := by
      have hProd := mul_le_mul hx hv (by norm_num) (by linarith : (0:ℝ)≤n)
      simpa using Real.sqrt_le_sqrt hProd
    have hEq : K n*v n = paperCp p*Real.sqrt ((n:ℝ)*v n) := by
      rw [paper_actual_product_scale hp (by omega : 0<n) hd.1,Real.sqrt_mul (Nat.cast_nonneg n)]
      ring
    refine hs.trans ?_
    rw [hEq]
    calc
      _ = (paperCp p/(18*P))*Real.sqrt ((n:ℝ)*v n)+1 := by ring
      _ ≤ _ := by linarith
  have h := retained_far_rate_tendsto_zero B v 144 (paperCp p/(18*P)+1) (by positivity) (by norm_num)
    (Eventually.of_forall fun n => by unfold B; positivity)
    (hd.mono fun _ h => h.2.1) (hd.mono fun _ h => h.2.2.le) hB
  have H := h.const_mul actualPairPrefactor
  rw [mul_zero] at H
  apply H.congr
  intro n
  dsimp only [B,v,K]
  ring

#print axioms paper_all_integer_far_packet_rate
end CenteredCubeSqrt
