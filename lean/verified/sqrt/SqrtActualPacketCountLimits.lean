import SqrtActualPacketDeletion

namespace CenteredCubeSqrt
open Set Filter Finset CubeSqrtOverlap
open scoped Topology BigOperators
set_option maxHeartbeats 1700000

noncomputable def paperCp (p : ℝ) : ℝ := 3*p/Real.sqrt 29

theorem paper_actual_product_scale {p : ℝ} (hp : 0<p) {n d : ℕ} (hn : 0<n) (hd : 0<d) :
    (paperPeriod d:ℝ)*paperV p n d = paperCp p*(Real.sqrt (paperV p n d)*Real.sqrt (n:ℝ)) := by
  let K := (paperPeriod d:ℝ)
  let v := paperV p n d
  have Kp : 0<K := by
    dsimp [K]
    exact_mod_cast (show 0<paperPeriod d by have := paperPeriod_one_le hd; omega)
  have NP : 0<(n:ℝ) := by exact_mod_cast hn
  have Vp : 0<v := by dsimp [v,paperV]; positivity
  have cp : 0<paperCp p := by unfold paperCp; positivity
  have T : K^2*v=9*p^2*(n:ℝ)/29 := by
    dsimp only [v,paperV,K]
    field_simp [show (paperPeriod d:ℝ)≠0 by exact Kp.ne']
  have R : (paperCp p)^2=9*p^2/29 := by
    unfold paperCp
    rw [div_pow, Real.sq_sqrt (by norm_num)]
    ring
  have H : K*Real.sqrt v=paperCp p*Real.sqrt (n:ℝ) := by
    have E : (K*Real.sqrt v)^2=(paperCp p*Real.sqrt (n:ℝ))^2 := by
      rw [mul_pow,mul_pow,R,Real.sq_sqrt Vp.le,Real.sq_sqrt NP.le,T]
      ring
    exact (sq_eq_sq₀ (by positivity) (by positivity)).mp E
  change K*v=paperCp p*(Real.sqrt v*Real.sqrt (n:ℝ))
  nth_rw 1 [←Real.sq_sqrt Vp.le]
  calc
    K*(Real.sqrt v)^2 = (K*Real.sqrt v)*Real.sqrt v := by ring
    _ = _ := by rw [H]; ring

theorem paper_actual_packet_count_limits {p : ℝ} (hp : 0<p) {d : ℕ→ℕ}
    (hd : ∀ᶠ n : ℕ in atTop, 0<d n ∧
      16*Real.log n≤paperV p n (d n) ∧ paperV p n (d n)<144*Real.log n)
    (R : ℕ→Finset ℕ) (N : ℕ) {P A : ℝ} (hP : 0<P) (hA : 0≤A)
    (hR : ∀ᶠ n in atTop, R n ⊆ Finset.range
      (rawPacketCount ((paperPeriod (d n):ℝ)*paperV p n (d n)/18) ((N:ℝ)*A) P))
    (hDel : ∀ᶠ n in atTop,
      let v := paperV p n (d n)
      let K := (paperPeriod (d n):ℝ)
      (((Finset.range (rawPacketCount (K*v/18) ((N:ℝ)*A) P) \ R n).card):ℝ)≤
        ((N:ℝ)+1)*(4*v^2)*(2*v/P+1)) :
    (Tendsto (fun n => ((R n).card:ℝ)/(Real.sqrt (paperV p n (d n))*Real.sqrt (n:ℝ)))
      atTop (𝓝 (paperCp p/(18*P)))) ∧
    (Tendsto (fun n => (2*P/((paperPeriod (d n):ℝ)*paperV p n (d n)))*((R n).card:ℝ))
      atTop (𝓝 (1/9))) ∧
    (∀ᶠ n in atTop, (R n).Nonempty) := by
  let K (n : ℕ) := (paperPeriod (d n):ℝ)
  let v (n : ℕ) := paperV p n (d n)
  let u (n : ℕ) := Real.sqrt (v n)
  let T : ℝ := (N:ℝ)*A
  let D (n : ℕ) := (((Finset.range (rawPacketCount (K n*v n/18) T P) \ R n).card):ℝ)
  have hK0 := paper_period_growth_of_choice hp d hd 0
  have hK : Tendsto K atTop atTop := by simpa only [pow_zero,div_one] using hK0
  have hv := paper_v_tendsto (v:=v) (hd.mono fun _ hn => hn.2.1)
  have hz : Tendsto (fun n => K n*v n/18) atTop atTop := by
    refine tendsto_atTop_mono' atTop ?_ (hK.const_mul_atTop (by norm_num : (0:ℝ)<1/18))
    filter_upwards [hK.eventually_ge_atTop (0:ℝ),hv.eventually_ge_atTop (1:ℝ)] with n a b
    have h := mul_le_mul_of_nonneg_left b a
    linarith
  have hk1 := paper_period_growth_of_choice hp d hd 2
  have hk2 : Tendsto (fun n => (v n)^2/K n) atTop (𝓝 0) := by
    simpa only [Function.comp_def,inv_div] using tendsto_inv_atTop_zero.comp hk1
  have he := paper_deletion_fraction_tendsto_zero K v D N P hP (hK.eventually_gt_atTop 0)
    (hv.eventually_ge_atTop 1) (Eventually.of_forall (fun _ => by unfold D; positivity)) hDel hk2
  have rr := retained_packet_ratio_limit (fun n => K n*v n/18) T P hz hP
    (by dsimp [T]; positivity) R hR he
  have cp : 0<paperCp p := by unfold paperCp; positivity
  have sc : ∀ᶠ n in atTop, K n*v n=paperCp p*(u n*Real.sqrt (n:ℝ)) := by
    filter_upwards [hd,eventually_gt_atTop 0] with n hn n0
    exact paper_actual_product_scale hp n0 hn.1
  have po : ∀ᶠ n in atTop, 0<u n*Real.sqrt (n:ℝ) := by
    filter_upwards [hv.eventually_gt_atTop 0,eventually_gt_atTop 0] with n vn nP
    dsimp [u]
    exact mul_pos (Real.sqrt_pos.2 vn) (Real.sqrt_pos.2 (by exact_mod_cast nP))
  exact ⟨paper_retained_count_normalized K v u R P (paperCp p) hP cp rr sc po,
    paper_retained_count_step_limit K v R P hP hz rr,
    retained_eventually_nonempty (fun n => K n*v n/18) P hP hz R rr⟩

#print axioms paper_actual_product_scale
#print axioms paper_actual_packet_count_limits
end CenteredCubeSqrt
