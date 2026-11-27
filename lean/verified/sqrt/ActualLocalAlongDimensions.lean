import SqrtActualPacketLocalLimit
import SqrtActualSourceRateTransfer
namespace CenteredCubeSqrt
open Set Filter MeasureTheory CubeSqrtOverlap
open scoped Topology BigOperators
set_option maxHeartbeats 1750000
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem local_actual_window_error_eventually_dims {l : Filter ℕ} {w p T s t : ℝ} (m : ℕ→ℕ)
    (hw : 4≤w) (hT : 0≤T) (hs : -T≤s) (hst : s≤t) (ht : t≤T)
    {b d : ℕ→ℕ} {v L0 : ℕ→ℝ} {X : ℕ→ℝ→ℝ→ℝ}
    (hK : Tendsto (fun n => (paperPeriod (d n):ℝ)) l atTop) (hv : Tendsto v l atTop)
    (hSource : ∀ᶠ n in l, ActualSafeLocalSource w p (v n) (b n) (d n) (L0 n) (X n))
    (hWin : ∀ᶠ n in l,
      let C := (paperPeriod (d n):ℝ)*v n
      L0 n∈paperScaleWindow ∧ (localLength (L0 n) C s)∈paperScaleWindow ∧
        (localLength (L0 n) C t)∈paperScaleWindow)
    (hScale : ∀ᶠ n : ℕ in l, (m n:ℝ)*p^2=(29/9)*(paperPeriod (d n):ℝ)^2*v n)
    (D : ℕ) (hD : 2*(2*T+1/w)+1≤D) :
    ∀ᶠ n in l,
      let K := (paperPeriod (d n):ℝ)
      let Ls := localLength (L0 n) (K*v n) s
      let Lt := localLength (L0 n) (K*v n) t
      |(m n:ℝ)*periodL2Sq (fun x => X n Lt x-X n Ls x)-(58/(9*(L0 n)^2))*pulseOverlap (1/w) s t s t 0|≤
        actualLocalMainError ((2:ℝ)^(b n)) K (v n) (1/w) T s t D := by
  have hC : Tendsto (fun n => (paperPeriod (d n):ℝ)*v n) l atTop := by
    refine tendsto_atTop_mono' l ?_ hK
    filter_upwards [hK.eventually_ge_atTop 0,hv.eventually_ge_atTop 1] with n hk hn
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hn hk
  have hw' : 0<w := by linarith
  have V := (hC.const_div_atTop (T+(1/w)/2)).eventually_lt_const (by norm_num : (0:ℝ)<1/4)
  filter_upwards [hSource,hWin,hScale,V,hv.eventually_gt_atTop (2*T+1/w)] with n src win sc hV hvn
  obtain ⟨mesh,hd,hz,g,hg,tβ,htβ,h1',safe,eq⟩ := src
  let _ : NeZero (2^d n-1) := hz
  rw [eq]
  exact actualLocalSource_finite hd g hg tβ htβ h1' hw mesh (m n) p T (L0 n) s t D hT hvn hD
    hV hs hst ht win.1 safe win.2.1 win.2.2 sc

theorem local_actual_window_increment_tendsto_dims {l : Filter ℕ} {w p T s t Lstar : ℝ} (m : ℕ→ℕ)
    (hw : 4≤w) (hT : 0≤T) (hs : -T≤s) (hst : s≤t) (ht : t≤T)
    {b d : ℕ→ℕ} {v L0 : ℕ→ℝ} {X : ℕ→ℝ→ℝ→ℝ}
    (hK : Tendsto (fun n => (paperPeriod (d n):ℝ)) l atTop) (hv : Tendsto v l atTop)
    (hSource : ∀ᶠ n in l, ActualSafeLocalSource w p (v n) (b n) (d n) (L0 n) (X n))
    (hWin : ∀ᶠ n in l,
      let C := (paperPeriod (d n):ℝ)*v n
      L0 n∈paperScaleWindow ∧ (localLength (L0 n) C s)∈paperScaleWindow ∧
        (localLength (L0 n) C t)∈paperScaleWindow)
    (hScale : ∀ᶠ n : ℕ in l, (m n:ℝ)*p^2=(29/9)*(paperPeriod (d n):ℝ)^2*v n)
    (hLstar : Lstar∈paperScaleWindow) (hL : Tendsto L0 l (𝓝 Lstar)) :
    Tendsto (fun n =>
      let C := (paperPeriod (d n):ℝ)*v n
      (m n:ℝ)*periodL2Sq (fun x => X n (localLength (L0 n) C t) x-X n (localLength (L0 n) C s) x))
      l (𝓝 ((58/(9*Lstar^2))*pulseOverlap (1/w) s t s t 0)) := by
  obtain ⟨D,hD⟩ := exists_nat_ge (2*(2*T+1/w)+1)
  have W := local_actual_window_error_eventually_dims m hw hT hs hst ht hK hv hSource hWin hScale D hD
  have hB : Tendsto (fun n => (2:ℝ)^(b n)) l atTop :=
    tendsto_atTop_mono' l (hSource.mono fun _ H => H.1.label_lower) hv
  have er := actualLocalMainError_tendsto hB hK hv (1/w) T s t D
  let O := pulseOverlap (1/w) s t s t 0
  have hStar : 0<Lstar := by linarith [hLstar.1]
  have den := (hL.pow 2).const_mul (9:ℝ)
  have comp := ((tendsto_const_nhds (x:=(58:ℝ))).div den (by positivity)).mul_const O
  have E := (Metric.tendsto_nhds.1 er)
  have G := (Metric.tendsto_nhds.1 comp)
  apply Metric.tendsto_nhds.2
  intro e he
  have h1 := E (e/2) (by positivity)
  have h2 := G (e/2) (by positivity)
  filter_upwards [W,h1,h2] with n hh h1n h2n
  dsimp only at hh ⊢
  rw [Real.dist_eq,sub_zero] at h1n
  rw [Real.dist_eq] at h2n ⊢
  dsimp only [O,Pi.div_apply] at h2n
  have eb := le_abs_self (actualLocalMainError ((2:ℝ)^(b n)) (paperPeriod (d n):ℝ) (v n) (1/w) T s t D)
  exact (abs_sub_le _ ((58/(9*(L0 n)^2))*pulseOverlap (1/w) s t s t 0) _).trans_lt (by linarith)


theorem local_actual_baseline_increment_bounded_dims {l : Filter ℕ} {w p T s t : ℝ} (m : ℕ→ℕ)
    (hw : 4≤w) (hT : 0≤T) (hs : -T≤s) (hst : s≤t) (ht : t≤T)
    {b d : ℕ→ℕ} {v L0 : ℕ→ℝ} {X : ℕ→ℝ→ℝ→ℝ}
    (hK : Tendsto (fun n => (paperPeriod (d n):ℝ)) l atTop) (hv : Tendsto v l atTop)
    (hSource : ∀ᶠ n in l, ActualSafeLocalSource w p (v n) (b n) (d n) (L0 n) (X n))
    (hWin : ∀ᶠ n in l,
      let C := (paperPeriod (d n):ℝ)*v n
      L0 n∈paperScaleWindow ∧ (localLength (L0 n) C s)∈paperScaleWindow ∧
        (localLength (L0 n) C t)∈paperScaleWindow)
    (hScale : ∀ᶠ n : ℕ in l, (m n:ℝ)*p^2=(29/9)*(paperPeriod (d n):ℝ)^2*v n) :
    ∃ C : ℝ, ∀ᶠ n in l,
      let D := (paperPeriod (d n):ℝ)*v n
      let Ls := localLength (L0 n) D s
      let Lt := localLength (L0 n) D t
      |(m n:ℝ)*periodInner (X n (L0 n)) (fun x => X n Lt x-X n Ls x)|≤C := by
  have hC : Tendsto (fun n => (paperPeriod (d n):ℝ)*v n) l atTop := by
    refine tendsto_atTop_mono' l ?_ hK
    filter_upwards [hK.eventually_ge_atTop 0,hv.eventually_ge_atTop 1] with n hk hn
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hn hk
  have hw' : 0<w := by linarith
  have V := (hC.const_div_atTop (T+(1/w)/2)).eventually_lt_const (by norm_num : (0:ℝ)<1/4)
  let C := (29/9)*28*(t-s) + ((29/9)*49+(29/3)*(16*localSpecConst+392)*T^2)/2
  refine ⟨C,?_⟩
  filter_upwards [hSource,hWin,hScale,V,hK.eventually_ge_atTop 1,hv.eventually_gt_atTop 0] with
    n src win sc hV hKn hvn
  obtain ⟨mesh,hd,hz,g,hg,tβ,htβ,h1',safe,eq⟩ := src
  let _ : NeZero (2^d n-1) := hz
  let K := (paperPeriod (d n):ℝ)
  let Ls := localLength (L0 n) (K*v n) s
  let Lt := localLength (L0 n) (K*v n) t
  have hδ : (1/w)/(K*v n)=paperMeshDelta w K (v n) := by
    unfold paperMeshDelta
    rw [div_div]
    ring
  have hKn' : 2≤(2^d n-1:ℕ) := by have := mesh.period_lower; unfold paperPeriod at this; omega
  have he : 0<1/w := by positivity
  have he4 : 1/w≤1/4 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hw
  have hBv : ((2^b n:ℕ):ℝ)≤2*v n := by push_cast; exact mesh.label_upper.le
  have hL0 : 1≤L0 n := by linarith [win.1.1]
  have hLs : 1≤Ls := by linarith [win.2.1.1]
  have hLt : 1≤Lt := by linarith [win.2.2.1]
  have V := actual_baseline_increment_finite (ordinalPhaseLabel hd g hg tβ) (paperMeshM (v n))
    (by positivity) hKn' (n:=m n) (p:=p) (v:=v n) (eps:=1/w) (T:=T) (L0:=L0 n)
    (s:=s) (t:=t) (by positivity) sc hvn he he4 hBv hT hV hs hst ht hL0 hLs hLt
  have R : (29/9)*28*(t-s) + ((29/9)*49+(29/3)*(16*localSpecConst+392)*T^2)/(2*K) ≤ C := by
    unfold C
    refine add_le_add le_rfl ?_
    apply div_le_div_of_nonneg_left
    · unfold localSpecConst; positivity
    · norm_num
    · linarith
  dsimp only at V ⊢
  rw [show (((2^d n-1:ℕ):ℝ))=(paperPeriod (d n):ℝ) by rfl,hδ] at V
  rw [eq]
  exact V.trans R


theorem packet_actual_local_limit_along_anchor_dims {l : Filter ℕ} {w p P A : ℝ} (m : ℕ→ℕ)
    (hw : 4≤w) (hA : 0≤A) {N : ℕ} {a c : Fin (N+1)} (hac : a≤c)
    {b d i : ℕ→ℕ} {R : ℕ→Finset ℕ} {X : ℕ→ℝ→ℝ→ℝ}
    (hK : Tendsto (fun n => (paperPeriod (d (m n)):ℝ)) l atTop)
    (hv : Tendsto (fun n => paperV p (m n) (d (m n))) l atTop)
    (hSource : ∀ᶠ n in l, ∀ j∈R (m n),
      let K := (paperPeriod (d (m n)):ℝ)
      let v := paperV p (m n) (d (m n))
      let L0 := paperPacketLength K v P A j 0
      ActualSafeLocalSource w p v (b (m n)) (d (m n)) L0 (X (m n)) ∧ L0∈paperScaleWindow ∧
      ∀ z : Fin (N+1), localLength L0 (K*v) ((z:ℝ)*A)∈paperScaleWindow)
    (hi : ∀ᶠ n in l, i n∈R (m n)) {Lstar : ℝ} (hLstar : Lstar∈paperScaleWindow)
    (hL : Tendsto (fun n => paperPacketLength (paperPeriod (d (m n))) (paperV p (m n) (d (m n))) P A (i n) 0)
      l (𝓝 Lstar)) :
    (Tendsto (fun n =>
      let K := (paperPeriod (d (m n)):ℝ)
      let v := paperV p (m n) (d (m n))
      (m n:ℝ)*periodL2Sq (fun x =>
        X (m n) (paperPacketLength K v P A (i n) c) x-X (m n) (paperPacketLength K v P A (i n) a) x))
      l (𝓝 ((58/(9*Lstar^2))*pulseOverlap (1/w) ((a:ℝ)*A) ((c:ℝ)*A) ((a:ℝ)*A) ((c:ℝ)*A) 0))) ∧
    (∃ C : ℝ, ∀ᶠ n in l,
      let K := (paperPeriod (d (m n)):ℝ)
      let v := paperV p (m n) (d (m n))
      |(m n:ℝ)*periodInner (X (m n) (paperPacketLength K v P A (i n) 0))
        (fun x => X (m n) (paperPacketLength K v P A (i n) c) x-X (m n) (paperPacketLength K v P A (i n) a) x)|≤C) := by
  let L0 (n : ℕ) := paperPacketLength (paperPeriod (d (m n))) (paperV p (m n) (d (m n))) P A (i n) 0
  let T := (N:ℝ)*A
  let s := (a:ℝ)*A
  let t := (c:ℝ)*A
  let v (n : ℕ) := paperV p (m n) (d (m n))
  have ht : t≤T := by
    dsimp [t,T]
    apply mul_le_mul_of_nonneg_right _ hA
    exact_mod_cast (show c.val≤N by omega)
  have hs : -T≤s := by
    have h : 0≤T := by unfold T; positivity
    have hs' : 0≤s := by unfold s; positivity
    linarith
  have hst : s≤t := by
    dsimp [s,t]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast (show a.val≤c.val from hac)) hA
  have hdata : ∀ᶠ n in l, ActualSafeLocalSource w p (v n) (b (m n)) (d (m n)) (L0 n) (X (m n)) ∧
      (let K := (paperPeriod (d (m n)):ℝ)
       L0 n∈paperScaleWindow ∧ localLength (L0 n) (K*v n) s∈paperScaleWindow ∧
       localLength (L0 n) (K*v n) t∈paperScaleWindow) := by
    filter_upwards [hSource,hi] with n h hR
    have D := h (i n) hR
    exact ⟨D.1,D.2.1,D.2.2 a,D.2.2 c⟩
  have sc : ∀ᶠ n : ℕ in l, (m n:ℝ)*p^2=(29/9)*(paperPeriod (d (m n)):ℝ)^2*v n := by
    filter_upwards [hdata] with n h
    obtain ⟨_,hd,_,_,_,_,_⟩ := h.1
    exact actual_v_exact_scale p hd
  have err := local_actual_window_increment_tendsto_dims m hw (T:=T) (by dsimp [T]; positivity)
    hs hst ht hK hv (hdata.mono fun _ H => H.1) (hdata.mono fun _ H => H.2) sc hLstar hL
  have bnd := local_actual_baseline_increment_bounded_dims m hw (T:=T) (by dsimp [T]; positivity)
    hs hst ht hK hv (hdata.mono fun _ H => H.1) (hdata.mono fun _ H => H.2) sc
  dsimp only [L0,s,t,v] at err bnd
  simp_rw [paper_packet_localLength_eq] at err bnd
  exact ⟨err,bnd⟩


theorem actual_q_rate_transfer_dims {l : Filter ℕ} (m : ℕ→ℕ) {v q a : ℕ→ℝ}
    (hv : Tendsto v l atTop) (hA : Tendsto (fun n => a n*v n) l (𝓝 0))
    (hV : Tendsto (fun n : ℕ => (v n)^2/(m n:ℝ)) l (𝓝 0))
    (C : ℝ) (_hC : 0≤C) (hQ : ∀ᶠ n in l, |q n-v n|≤C) :
    Tendsto (fun n => q n/v n) l (𝓝 1) ∧
    Tendsto (fun n => a n*q n) l (𝓝 0) ∧
    Tendsto (fun n : ℕ => q n/(m n:ℝ)) l (𝓝 0) ∧
    Tendsto (fun n : ℕ => (q n)^2/(m n:ℝ)) l (𝓝 0) := by
  have hVpos := hv.eventually_gt_atTop (0:ℝ)
  have ratio : Tendsto (fun n => q n/v n) l (𝓝 1) := by
    apply Metric.tendsto_nhds.2
    intro e eh
    have ht := (hv.const_div_atTop C).eventually_lt_const eh
    filter_upwards [ht,hQ,hVpos] with n he hq hp
    rw [Real.dist_eq,show q n/v n-1=(q n-v n)/v n by field_simp,
      abs_div,abs_of_pos hp]
    exact lt_of_le_of_lt (div_le_div_of_nonneg_right hq hp.le) he
  have hR : Tendsto (fun n => a n*q n) l (𝓝 0) := by
    have H := hA.mul ratio
    rw [zero_mul] at H
    refine H.congr' ?_
    filter_upwards [hVpos] with n hn
    field_simp
  have h2 : Tendsto (fun n : ℕ => (q n)^2/(m n:ℝ)) l (𝓝 0) := by
    have H := hV.mul (ratio.pow 2)
    rw [zero_mul] at H
    refine H.congr' ?_
    filter_upwards [hVpos] with n hn
    simp only [div_eq_mul_inv]
    have E : (v n)^2*((v n)^2)⁻¹=1 := mul_inv_cancel₀ (by positivity)
    calc
      _ = ((v n)^2*((v n)^2)⁻¹)*((q n)^2*(m n:ℝ)⁻¹) := by ring
      _ = _ := by rw [E,one_mul]
  have h1 : Tendsto (fun n : ℕ => q n/(m n:ℝ)) l (𝓝 0) := by
    have H := (hV.mul (tendsto_inv_atTop_zero.comp hv)).mul ratio
    simp only [zero_mul] at H
    refine H.congr' ?_
    filter_upwards [hVpos] with n hn
    change (v n)^2/(m n:ℝ)*(v n)⁻¹*(q n/v n)=q n/(m n:ℝ)
    simp only [div_eq_mul_inv]
    have E : (v n)^2*((v n)⁻¹)^2=1 := by rw [←mul_pow,mul_inv_cancel₀ hn.ne',one_pow]
    calc
      _ = ((v n)^2*((v n)⁻¹)^2)*(q n*(m n:ℝ)⁻¹) := by ring
      _ = _ := by rw [E,one_mul]
  exact ⟨ratio,hR,h1,h2⟩

#print axioms local_actual_window_error_eventually_dims
#print axioms local_actual_window_increment_tendsto_dims
#print axioms local_actual_baseline_increment_bounded_dims
#print axioms packet_actual_local_limit_along_anchor_dims
#print axioms actual_q_rate_transfer_dims
end CenteredCubeSqrt
