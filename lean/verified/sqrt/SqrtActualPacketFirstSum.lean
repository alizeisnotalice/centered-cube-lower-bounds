import SqrtAllIntegerPackets

namespace CenteredCubeSqrt
open Set Filter Finset CubeSqrtOverlap
open scoped Topology BigOperators
set_option maxHeartbeats 1700000

theorem actual_packet_score_first_sum {p w P A α β : ℝ} (hp : 0<p) (hP : 0<P) (hA : 0≤A)
    (hα : 0≤α) {d b : ℕ→ℕ} {N : ℕ} {R : ℕ→Finset ℕ} (score : ℕ→ℕ→ℝ)
    (hd : ∀ᶠ n : ℕ in atTop, 0<d n ∧
      16*Real.log n≤paperV p n (d n) ∧ paperV p n (d n)<144*Real.log n)
    (hR : ∀ᶠ n in atTop, ActualPacketChoice w (paperV p n (d n)) P A (b n) (d n) N (R n))
    (hScore : ∀ᶠ n in atTop, ∀ i∈R n, α/(paperPacketLength (paperPeriod (d n))
        (paperV p n (d n)) P A i 0)^2-β≤score n i)
    (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ n in atTop, (paperCp p/(2*P))*(α*(9/10-9/11)-β*(1/9))-ε ≤
      (∑ i∈R n,score n i)/(Real.sqrt (paperV p n (d n))*Real.sqrt (n:ℝ)) := by
  let K (n : ℕ) := (paperPeriod (d n):ℝ)
  let v (n : ℕ) := paperV p n (d n)
  let u (n : ℕ) := Real.sqrt (v n)
  let Δ (n : ℕ) := 2*P/(K n*v n)
  let T : ℝ := (N:ℝ)*A
  let B (n : ℕ) := rawPacketCount (K n*v n/18) T P
  let Dc (n : ℕ) := (((range (B n) \ R n).card):ℝ)
  have hK0 := paper_period_growth_of_choice hp d hd 0
  have hK : Tendsto K atTop atTop := by simpa only [pow_zero,div_one] using hK0
  have hv := paper_v_tendsto (v:=v) (hd.mono fun _ h => h.2.1)
  have hz : Tendsto (fun n => K n*v n/18) atTop atTop := by
    refine tendsto_atTop_mono' atTop ?_ (hK.const_mul_atTop (by norm_num : (0:ℝ)<1/18))
    filter_upwards [hK.eventually_ge_atTop 0,hv.eventually_ge_atTop 1] with n hk hn
    linarith [mul_le_mul_of_nonneg_left hn hk]
  have TD : 0≤T := by dsimp [T]; positivity
  have k2 := paper_period_growth_of_choice hp d hd 2
  have k2i : Tendsto (fun n => (v n)^2/K n) atTop (𝓝 0) := by
    simpa only [Function.comp_def,inv_div] using tendsto_inv_atTop_zero.comp k2
  have raw : ∀ᶠ n in atTop, R n⊆range (B n) := hR.mono fun _ H => H.2.1
  have del : ∀ᶠ n in atTop, Dc n≤((N:ℝ)+1)*(4*(v n)^2)*(2*v n/P+1) :=
    hR.mono fun _ H => H.2.2.1
  have Hdel := paper_deletion_fraction_tendsto_zero K v Dc N P hP (hK.eventually_gt_atTop 0)
    (hv.eventually_ge_atTop 1) (Eventually.of_forall (fun _ => by unfold Dc; positivity)) del k2i
  have scaled := paper_scaled_deletions_tendsto K v Dc P hz Hdel
  have End := paper_raw_endpoint_tendsto K v T P hP TD hz
  have Count := (paper_actual_packet_count_limits hp hd R N hP hA raw del).2.1
  have Δp : ∀ᶠ n in atTop, 0≤Δ n := by
    filter_upwards [hK.eventually_gt_atTop 0,hv.eventually_gt_atTop 0] with n hk hn
    dsimp [Δ]
    positivity
  have C : ∀ᶠ n in atTop, ∀ i∈R n, α/(10/9+(i:ℝ)*Δ n)^2-β≤score n i := by
    filter_upwards [hScore] with n hs
    intro i hi
    have E : 10/9+(i:ℝ)*Δ n=paperPacketLength (K n) (v n) P A i 0 := by
      unfold Δ paperPacketLength
      simp only [Nat.cast_zero,zero_mul,add_zero]
      ring
    rw [E]
    exact hs i hi
  let c := paperCp p/(2*P)
  have hc : 0<c := by dsimp [c,paperCp]; positivity
  have Count' : Tendsto (fun n => Δ n*((R n).card:ℝ)) atTop (𝓝 ((11:ℝ)/9-10/9)) := by
    convert Count using 1
    norm_num
  have Q := reinforced_first_sum_inverse_square (10/9) (11/9) α β (by norm_num) (by norm_num)
    hα Δ B R score Δp raw End scaled Count' C (ε/c) (by positivity)
  filter_upwards [Q,hd,eventually_gt_atTop (0:ℕ),hv.eventually_gt_atTop 0] with n h hn hN hvn
  have hScale : K n*v n=paperCp p*(u n*Real.sqrt (n:ℝ)) :=
    paper_actual_product_scale hp hN hn.1
  have hp' : 0<paperCp p := by unfold paperCp; positivity
  have hD : 0<u n*Real.sqrt (n:ℝ) := by
    dsimp [u]
    exact mul_pos (Real.sqrt_pos.2 hvn) (Real.sqrt_pos.2 (by exact_mod_cast hN))
  have Q := mul_le_mul_of_nonneg_left h hc.le
  have ez : c*(ε/c)=ε := by field_simp
  have eL : c*(α*(1/(10/9)-1/(11/9))-β*(11/9-10/9)-ε/c)=
      c*(α*(9/10-9/11)-β*(1/9))-ε := by
    rw [mul_sub,ez]
    ring
  rw [eL] at Q
  have eR : c*(Δ n*(∑ i∈R n,score n i))=
      (∑ i∈R n,score n i)/(u n*Real.sqrt (n:ℝ)) := by
    unfold c Δ
    rw [hScale]
    field_simp [hD.ne',hP.ne',hp'.ne']
  rw [eR] at Q
  exact Q

#print axioms actual_packet_score_first_sum
end CenteredCubeSqrt
