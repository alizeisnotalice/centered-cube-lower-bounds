import SqrtPaperParameterChoice
import SqrtLabelBudget

namespace CenteredCubeSqrt
open Filter Set
open scoped Topology
set_option maxHeartbeats 1400000

theorem log_power_div_nat_tendsto (j : ℕ) :
    Tendsto (fun n : ℕ => (Real.log (n:ℝ))^j/(n:ℝ)) atTop (𝓝 0) := by
  have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 j one_ne_zero).comp
    (tendsto_natCast_atTop_atTop (R:=ℝ))
  simpa only [Function.comp_def,one_mul,add_zero] using h

theorem paper_seed_eventually {p : ℝ} (hp : 0<p) :
    ∀ᶠ n : ℕ in atTop, 1<n ∧ 16*Real.log n≤9*p^2*(n:ℝ)/29 := by
  have h := log_power_div_nat_tendsto 1
  have c : 0< (9*p^2/29)/16 := by positivity
  have e := h.eventually_lt_const c
  filter_upwards [e,eventually_gt_atTop 1] with n H hn
  have hn' : 0<(n:ℝ) := by exact_mod_cast (show 0<n by omega)
  rw [pow_one] at H
  have W := (div_lt_iff₀ hn').1 H
  exact ⟨hn,by linarith⟩

theorem paper_log_nat_tendsto_atTop :
    Tendsto (fun n : ℕ => Real.log (n:ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))

theorem paper_dyadic_choice_eventually {p : ℝ} (hp : 0<p) :
    ∃ d : ℕ→ℕ, ∀ᶠ n : ℕ in atTop,
      0<d n ∧ 16*Real.log n≤paperV p n (d n) ∧
      paperV p n (d n)<144*Real.log n ∧ paperV p n (d n+1)<16*Real.log n ∧
      ∀ e : ℕ, 0<e → 16*Real.log n≤paperV p n e → e≤d n := by
  classical
  let P (n j : ℕ) := 0<j ∧ 16*Real.log n≤paperV p n j ∧
      paperV p n j<144*Real.log n ∧ paperV p n (j+1)<16*Real.log n ∧
      ∀ e : ℕ, 0<e → 16*Real.log n≤paperV p n e → e≤j
  let d (n : ℕ) := if H : ∃ j, P n j then H.choose else 1
  refine ⟨d,?_⟩
  filter_upwards [paper_seed_eventually hp] with n hn
  have H : ∃ j, P n j := paper_v_period_prescription hp hn.1 hn.2
  have W := H.choose_spec
  dsimp [d]
  rw [dite_eq_left H]
  exact W

theorem paper_v_tendsto {v : ℕ→ℝ}
    (h : ∀ᶠ n : ℕ in atTop, 16*Real.log (n:ℝ)≤v n) :
    Tendsto v atTop atTop :=
  tendsto_atTop_mono' atTop h (paper_log_nat_tendsto_atTop.const_mul_atTop (by norm_num : (0:ℝ)<16))

theorem paper_period_growth_of_choice {p : ℝ} (hp : 0<p) (d : ℕ→ℕ)
    (h : ∀ᶠ n : ℕ in atTop, 0<d n ∧
      16*Real.log n≤paperV p n (d n) ∧ paperV p n (d n)<144*Real.log n)
    (j : ℕ) :
    Tendsto (fun n => ((paperPeriod (d n):ℕ):ℝ)/(paperV p n (d n))^j) atTop atTop := by
  let v (n : ℕ) := paperV p n (d n)
  let K (n : ℕ) := ((paperPeriod (d n):ℕ):ℝ)
  have hkt : ∀ᶠ n in atTop, 0<K n := h.mono fun n hn => by
    dsimp [K]
    exact_mod_cast (show 0<paperPeriod (d n) by have := paperPeriod_one_le hn.1; omega)
  have hv := paper_v_tendsto (v:=v) (h.mono fun _ hn => hn.2.1)
  have hvp := (tendsto_atTop.1 hv 1).mono fun n hn => (show 0<v n by linarith)
  have H := (log_power_div_nat_tendsto (2*j+1)).const_mul
    ((29/(9*p^2))*(144:ℝ)^(2*j+1))
  have H' : Tendsto (fun n : ℕ => (29/(9*p^2))*(144:ℝ)^(2*j+1)*
      ((Real.log (n:ℝ))^(2*j+1)/(n:ℝ))) atTop (𝓝 0) := by simpa only [mul_zero] using H
  have upper : ∀ᶠ n in atTop, (v n^j/K n)^2≤(29/(9*p^2))*(144:ℝ)^(2*j+1)*
        ((Real.log (n:ℝ))^(2*j+1)/(n:ℝ)) := by
    filter_upwards [h,hkt,hvp,eventually_gt_atTop 1] with n hn hK hV hN
    have nP : 0<(n:ℝ) := by exact_mod_cast (show 0<n by omega)
    have pP : p≠0 := hp.ne'
    have identity : v n*(K n)^2=9*p^2*(n:ℝ)/29 := by
      dsimp only [v,paperV,K]
      field_simp [show (paperPeriod (d n):ℝ)≠0 by exact hK.ne']
    have e : (v n^j/K n)^2=(29/(9*p^2))*(v n^(2*j+1)/(n:ℝ)) := by
      have e₂ : (v n^j)^2=v n^(2*j) := by rw [←pow_mul,mul_comm j 2]
      rw [div_pow,e₂,pow_succ]
      field_simp [hK.ne',pP,nP.ne']
      calc
        _ = (v n^(2*j))*(9*p^2*(n:ℝ)) := by ring
        _ = (v n^(2*j))*(29*(v n*(K n)^2)) := by rw [identity]; ring
        _ = _ := by ring
    rw [e]
    have vv : v n≤144*Real.log n := hn.2.2.le
    have P := pow_le_pow_left₀ hV.le vv (2*j+1)
    rw [mul_pow] at P
    have T := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right P nP.le)
      (show 0≤29/(9*p^2) by positivity)
    convert T using 1
    ring
  have nonneg : ∀ᶠ n in atTop, 0≤(v n^j/K n)^2 := Eventually.of_forall (fun _ => sq_nonneg _)
  have sqLim : Tendsto (fun n => (v n^j/K n)^2) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds H' nonneg upper
  have qLim : Tendsto (fun n => v n^j/K n) atTop (𝓝 0) := by
    have H := Real.continuous_sqrt.continuousAt.tendsto.comp sqLim
    rw [Real.sqrt_zero] at H
    apply H.congr'
    filter_upwards [hkt,hvp] with n a b
    exact Real.sqrt_sq (by positivity)
  have qPos : ∀ᶠ n in atTop, 0<v n^j/K n := by
    filter_upwards [hkt,hvp] with n a b
    positivity
  have qRight : Tendsto (fun n => v n^j/K n) atTop (𝓝[>] (0:ℝ)) :=
    tendsto_nhdsWithin_iff.2 ⟨qLim,qPos⟩
  have hi := tendsto_inv_nhdsGT_zero.comp qRight
  simpa only [Function.comp_def,inv_div] using hi

#print axioms paper_dyadic_choice_eventually
#print axioms paper_period_growth_of_choice
end CenteredCubeSqrt
