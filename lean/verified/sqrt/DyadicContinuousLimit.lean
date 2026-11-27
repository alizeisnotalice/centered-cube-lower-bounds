import BrownianDyadicClock

namespace CubeBrownian
open Filter
open scoped NNReal Topology
set_option maxHeartbeats 2500000

def DyadicGood (F : ℝ≥0 → ℝ) : Prop :=
  ∀ M : ℕ, ∀ᶠ m in atTop, ∀ k < M*2^m,
    |F (dyadicClock m (k+1))-F (dyadicClock m k)|≤dyadicError m

noncomputable def dyadicApprox (F : ℝ≥0 → ℝ) (m : ℕ) (t : ℝ≥0) : ℝ :=
  F (dyadicClock m (dyadicIndex m t))

noncomputable def dyadicLimit (F : ℝ≥0 → ℝ) (t : ℝ≥0) : ℝ := by
  classical
  exact if h : ∃ x, Tendsto (fun m => dyadicApprox F m t) atTop (𝓝 x) then h.choose else 0

theorem dyadicError_nonneg (m : ℕ) : 0≤dyadicError m := by unfold dyadicError; positivity

theorem dyadicError_succ_le (m : ℕ) : dyadicError (m+1)≤dyadicError m := by
  unfold dyadicError
  rw [pow_succ]
  exact mul_le_of_le_one_right (by positivity) (by norm_num)

theorem dyadic_approx_succ {F : ℝ≥0 → ℝ} {m M : ℕ}
    (hG : ∀ k < M*2^(m+1), |F (dyadicClock (m+1) (k+1))-F (dyadicClock (m+1) k)|≤dyadicError (m+1))
    {t : ℝ≥0} (ht : (t:ℝ)<M) :
    dist (dyadicApprox F m t) (dyadicApprox F (m+1) t) ≤ dyadicError m := by
  have hi := dyadicIndex_lt_compact (m:=m+1) ht
  rcases dyadicIndex_step m t with h0|h1
  · unfold dyadicApprox
    rw [h0,dyadicClock_even,dist_self]
    exact dyadicError_nonneg m
  · let k := 2*dyadicIndex m t
    have hk : k<M*2^(m+1) := by omega
    have h0 := hG k hk
    unfold dyadicApprox
    rw [h1,←dyadicClock_even m (dyadicIndex m t),Real.dist_eq,abs_sub_comm]
    exact h0.trans (dyadicError_succ_le m)

theorem dyadic_approx_same_scale {F : ℝ≥0 → ℝ} {m M : ℕ}
    (hG : ∀ k < M*2^m, |F (dyadicClock m (k+1))-F (dyadicClock m k)|≤dyadicError m)
    {s t : ℝ≥0} (hs : (s:ℝ)<M) (ht : (t:ℝ)<M)
    (h : dist s t < (1:ℝ)/(2:ℝ)^m) :
    dist (dyadicApprox F m s) (dyadicApprox F m t) ≤ dyadicError m := by
  wlog hst : (s:ℝ) ≤ (t:ℝ) generalizing s t
  · rw [dist_comm]
    exact this ht hs (by rwa [dist_comm]) (le_of_not_ge hst)
  change dist (s:ℝ) (t:ℝ)<_ at h
  rw [Real.dist_eq,abs_sub_comm,abs_of_nonneg (sub_nonneg.mpr hst)] at h
  rcases dyadicIndex_close_le hst h with h0|h1
  · unfold dyadicApprox
    rw [h0,dist_self]
    exact dyadicError_nonneg m
  · unfold dyadicApprox
    rw [h1,Real.dist_eq,abs_sub_comm]
    exact hG _ (dyadicIndex_lt_compact (m:=m) hs)

theorem dyadic_approx_limit_exists {F : ℝ≥0 → ℝ} (hF : DyadicGood F) (t : ℝ≥0) :
    ∃ x, Tendsto (fun m => dyadicApprox F m t) atTop (𝓝 x) := by
  obtain ⟨M,hM⟩ := exists_nat_gt (t:ℝ)
  obtain ⟨N,hN⟩ := eventually_atTop.1 (hF M)
  let s (n : ℕ) := dyadicApprox F (n+N) t
  have hs (n : ℕ) : dist (s n) (s (n+1))≤dyadicError N*(7/8:ℝ)^n := by
    have hP := dyadic_approx_succ (hN (n+N+1) (by omega)) hM
    simpa only [s, Nat.add_right_comm n 1 N, dyadicError, pow_add, mul_comm] using hP
  have hc : CauchySeq s := cauchySeq_of_le_geometric (7/8:ℝ) (dyadicError N) (by norm_num) hs
  obtain ⟨x,hx⟩ := cauchySeq_tendsto_of_complete hc
  exact ⟨x,(tendsto_add_atTop_iff_nat N).1 hx⟩

theorem dyadic_approx_tendsto_limit {F : ℝ≥0 → ℝ} (hF : DyadicGood F) (t : ℝ≥0) :
    Tendsto (fun m => dyadicApprox F m t) atTop (𝓝 (dyadicLimit F t)) := by
  have h := dyadic_approx_limit_exists hF t
  unfold dyadicLimit
  rw [dite_eq_left h]
  exact h.choose_spec

theorem dyadic_approx_limit_bound {F : ℝ≥0 → ℝ} (hF : DyadicGood F) {M m : ℕ}
    (hG : ∀ j≥m, ∀ k < M*2^j, |F (dyadicClock j (k+1))-F (dyadicClock j k)|≤dyadicError j)
    {t : ℝ≥0} (ht : (t:ℝ)<M) :
    dist (dyadicApprox F m t) (dyadicLimit F t) ≤ 8*dyadicError m := by
  let s (n : ℕ) := dyadicApprox F (n+m) t
  have hs (n : ℕ) : dist (s n) (s (n+1))≤dyadicError m*(7/8:ℝ)^n := by
    have hP := dyadic_approx_succ (hG (n+m+1) (by omega)) ht
    simpa only [s,Nat.add_right_comm n 1 m,dyadicError,pow_add,mul_comm] using hP
  have hT : Tendsto s atTop (𝓝 (dyadicLimit F t)) :=
    (tendsto_add_atTop_iff_nat m).2 (dyadic_approx_tendsto_limit hF t)
  have H := dist_le_of_le_geometric_of_tendsto₀ (7/8:ℝ) (dyadicError m) (by norm_num) hs hT
  simp only [s,zero_add] at H
  convert H using 1 <;> ring

theorem dyadicLimit_continuous {F : ℝ≥0 → ℝ} (hF : DyadicGood F) :
    Continuous (dyadicLimit F) := by
  rw [continuous_iff_continuousAt]
  intro t
  rw [Metric.continuousAt_iff]
  intro ε hε
  obtain ⟨M,hM⟩ := exists_nat_gt ((t:ℝ)+1)
  have hT : (t:ℝ)<M := by linarith
  obtain ⟨N,hN⟩ := eventually_atTop.1 (hF M)
  have hδ : Tendsto dyadicError atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have h17 := (hδ.const_mul 17).eventually_lt_const (show 17*0<ε by linarith)
  obtain ⟨m,hm,hSmall⟩ := ((eventually_ge_atTop N).and h17).exists
  have hGood j (hj : m≤j) := hN j (hm.trans hj)
  let r : ℝ := min 1 (1/(2:ℝ)^m)
  refine ⟨r,lt_min (by norm_num) (by positivity),?_⟩
  intro s hs
  have hst : dist s t < 1/(2:ℝ)^m := hs.trans_le (min_le_right _ _)
  have hs₀ : (s:ℝ)<M := by
    have h1 := hs.trans_le (min_le_left (1:ℝ) (1/(2:ℝ)^m))
    change dist (s:ℝ) (t:ℝ)<1 at h1
    rw [Real.dist_eq,abs_lt] at h1
    linarith only [h1.2,hM]
  have Hs := dyadic_approx_limit_bound hF hGood hs₀
  have Ht := dyadic_approx_limit_bound hF hGood hT
  have Hst := dyadic_approx_same_scale (hGood m le_rfl) hs₀ hT hst
  have h₁ := dist_triangle (dyadicLimit F s) (dyadicApprox F m s) (dyadicLimit F t)
  have h₂ := dist_triangle (dyadicApprox F m s) (dyadicApprox F m t) (dyadicLimit F t)
  rw [dist_comm (dyadicLimit F s) (dyadicApprox F m s)] at h₁
  linarith only [h₁,h₂,Hs,Ht,Hst,hSmall]

#print axioms dyadic_approx_tendsto_limit
#print axioms dyadicLimit_continuous
end CubeBrownian
