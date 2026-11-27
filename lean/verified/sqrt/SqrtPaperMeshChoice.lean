import SqrtPaperParameterGrowth

namespace CenteredCubeSqrt
open Filter Set
open scoped Topology
set_option maxHeartbeats 1500000

noncomputable def paperMeshM (v : ℝ) : ℕ := ⌈Real.sqrt v⌉₊
noncomputable def paperMeshDelta (w K v : ℝ) : ℝ := 1/(w*K*v)

structure PaperMeshParameters (w v : ℝ) (b d : ℕ) : Prop where
  v_ge_four : 4 < v
  label_ge_two : 2 ≤ b
  label_rank : 2*b ≤ d
  label_lower : v≤(2:ℝ)^b
  label_upper : (2:ℝ)^b<2*v
  label_minimal : ∀ e : ℕ, v≤(2:ℝ)^e → b≤e
  period_lower : 18≤paperPeriod d
  label_budget : labelBudget ((2:ℝ)^b)<(2:ℝ)^d
  mesh_lower : 0<paperMeshM v
  mesh_le_v : (paperMeshM v:ℝ)≤v
  mesh_lt_period : paperMeshM v<paperPeriod d
  mesh_sqrt_lower : Real.sqrt v≤paperMeshM v
  mesh_sqrt_upper : (paperMeshM v:ℝ)<Real.sqrt v+1
  delta_positive : 0<paperMeshDelta w (paperPeriod d) v
  delta_small : paperMeshDelta w (paperPeriod d) v<1/(2*((2:ℝ)^b)*(paperPeriod d:ℝ))
  delta_trivial : paperMeshDelta w (paperPeriod d) v<1
  delta_period : (paperPeriod d:ℝ)*paperMeshDelta w (paperPeriod d) v≤1

theorem paperMeshParameters_of_binary {w v : ℝ} (hw : 4≤w) (hv : 4<v) (b d : ℕ)
    (hlo : v≤(2:ℝ)^b) (hhi : (2:ℝ)^b<2*v)
    (hmin : ∀ e : ℕ, v≤(2:ℝ)^e → b≤e)
    (hK : 49≤(paperPeriod d:ℝ)/v^4) :
    PaperMeshParameters w v b d := by
  let B := (2:ℝ)^b
  let K := (paperPeriod d:ℝ)
  let M := paperMeshM v
  let δ := paperMeshDelta w K v
  have hB : 4≤B := by linarith
  have hB' : 1≤B := by linarith
  have hb : 2≤b := by
    by_contra! h
    have T : (2:ℝ)^b≤2 := by
      interval_cases b <;> norm_num
    dsimp [B] at hB
    linarith
  have hV : 1≤v := by linarith
  have hVp : 0<v := by linarith
  have hV4 : v≤v^4 := by
    have Q := pow_le_pow_right₀ hV (show 1≤(4:ℕ) by decide)
    simpa only [pow_one] using Q
  have K4 : 49*v^4≤K := (le_div_iff₀ (by positivity : 0<v^4)).1 hK
  have Klo : 18≤K := by linarith
  have Kpos : 0<K := by linarith
  have Kvs : v<K := by linarith
  have BK : 3*B^4<K := by
    have Q := pow_lt_pow_left₀ hhi (show 0≤B by positivity) (by decide : 4≠0)
    rw [mul_pow] at Q
    dsimp [K]
    have h := pow_pos hVp 4
    linarith
  have KP1 : K+1=(2:ℝ)^d := by
    have e : paperPeriod d+1=2^d := by
      unfold paperPeriod
      have h : 0<(2:ℕ)^d := by positivity
      omega
    dsimp only [K]
    exact_mod_cast e
  have hbudget := (labelBudget_lt_three B hB).trans (BK.trans (by linarith : K<(2:ℝ)^d))
  have hdim : 2*b≤d := by
    apply le_of_lt
    apply (pow_lt_pow_iff_right₀ (show 1<(2:ℝ) by norm_num)).1
    rw [mul_comm 2 b,pow_mul]
    have h24 := pow_le_pow_right₀ hB' (show (2:ℕ)≤4 by decide)
    change B^2<(2:ℝ)^d
    have hb4 : 0≤B^4 := by positivity
    linarith
  have hKnat : 18≤paperPeriod d := by dsimp [K] at Klo; exact_mod_cast Klo
  have hMsqrt : Real.sqrt v≤(M:ℝ) := Nat.le_ceil _
  have hMsqrt' : (M:ℝ)<Real.sqrt v+1 := Nat.ceil_lt_add_one (Real.sqrt_nonneg v)
  have hM0 : 0<M := by
    have H : 0<(M:ℝ) := (Real.sqrt_pos.2 hVp).trans_le hMsqrt
    exact_mod_cast H
  have hMv : (M:ℝ)≤v := by
    have hS : Real.sqrt v≤v/2 := (Real.sqrt_le_iff.mpr ⟨by positivity,by nlinarith⟩)
    linarith
  have hMK : M<paperPeriod d := by
    have H : (M:ℝ)<(paperPeriod d:ℝ) := hMv.trans_lt Kvs
    exact_mod_cast H
  have hwP : 0<w := by linarith
  have hδ0 : 0<δ := by unfold δ paperMeshDelta; positivity
  have hδB : δ<1/(2*B*K) := by
    unfold δ paperMeshDelta
    apply div_lt_div_of_pos_left (by norm_num) (by positivity)
    have h : 2*B<w*v := by linarith [mul_le_mul_of_nonneg_right hw hVp.le]
    nlinarith [mul_lt_mul_of_pos_right h Kpos]
  have hδ1 : δ<1 := by
    refine hδB.trans_le ?_
    apply (div_le_iff₀ (by positivity)).2
    have h := mul_le_mul hB' (show 1≤K by linarith) (by norm_num) (show 0≤B by positivity)
    nlinarith
  have hδK : K*δ≤1 := by
    unfold δ paperMeshDelta
    rw [mul_one_div]
    refine (div_le_iff₀ (by positivity)).2 ?_
    have h : 1≤w*v := by nlinarith [mul_le_mul hw hV (by norm_num) hwP.le]
    nlinarith [mul_le_mul_of_nonneg_right h Kpos.le]
  exact ⟨hv,hb,hdim,hlo,hhi,hmin,hKnat,hbudget,hM0,hMv,hMK,hMsqrt,hMsqrt',hδ0,hδB,hδ1,hδK⟩

theorem paper_binary_mesh_eventually {w : ℝ} (hw : 4≤w) (v : ℕ→ℝ) (d : ℕ→ℕ)
    (hv : Tendsto v atTop atTop)
    (hK : Tendsto (fun n => (paperPeriod (d n):ℝ)/(v n)^4) atTop atTop) :
    ∃ b : ℕ→ℕ, ∀ᶠ n in atTop, PaperMeshParameters w (v n) (b n) (d n) := by
  classical
  let P (n b : ℕ) := 0<b ∧ v n≤(2:ℝ)^b ∧ (2:ℝ)^b<2*v n ∧
      ∀ e : ℕ, v n≤(2:ℝ)^e → b≤e
  let b (n : ℕ) := if H : ∃ j, P n j then H.choose else 2
  refine ⟨b,?_⟩
  filter_upwards [tendsto_atTop.1 hv 5,tendsto_atTop.1 hK 49] with n vi ki
  have vv : 4<v n := by linarith
  have H : ∃ j, P n j := paper_first_binary_ge (by linarith)
  have hb := H.choose_spec
  dsimp [b]
  rw [dite_eq_left H]
  exact paperMeshParameters_of_binary hw vv _ _ hb.2.1 hb.2.2.1 hb.2.2.2 ki

#print axioms paperMeshParameters_of_binary
#print axioms paper_binary_mesh_eventually
end CenteredCubeSqrt
