import SqrtActualLocalAsymptoticError
import SqrtWindowPulseNormExact

namespace CenteredCubeSqrt
open Set Filter MeasureTheory
open scoped Topology BigOperators
set_option maxHeartbeats 2400000
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

def ActualSafeLocalSource (w p v : ℝ) (b d : ℕ) (L0 : ℝ) (X : ℝ→ℝ→ℝ) : Prop :=
  PaperMeshParameters w v b d ∧
  ∃ (hd : 0<d) (hK : NeZero (2^d-1)) (g : (LabelField d)ˣ)
    (hg : orderOf g=2^d-1) (tβ : Fin b→LabelField d),
    LinearIndependent (ZMod 2) tβ ∧
    (phaseState hd g hg 1 : LabelField d) ∉ labelRatioSet tβ ∧
    actualSafeLifts hd g hg tβ L0 ∧
    X=@actualWindowPerturbation (2^b) (2^d-1) hK
      (@ordinalPhaseLabel b d hd g hg tβ) (paperMeshM v) p (paperMeshDelta w (paperPeriod d) v)

theorem local_actual_window_error_eventually {l : Filter ℕ} {w p T s t : ℝ}
    (hw : 4≤w) (hT : 0≤T) (hs : -T≤s) (hst : s≤t) (ht : t≤T)
    {b d : ℕ→ℕ} {v L0 : ℕ→ℝ} {X : ℕ→ℝ→ℝ→ℝ}
    (hK : Tendsto (fun n => (paperPeriod (d n):ℝ)) l atTop) (hv : Tendsto v l atTop)
    (hSource : ∀ᶠ n in l, ActualSafeLocalSource w p (v n) (b n) (d n) (L0 n) (X n))
    (hWin : ∀ᶠ n in l,
      let C := (paperPeriod (d n):ℝ)*v n
      L0 n∈paperScaleWindow ∧ (localLength (L0 n) C s)∈paperScaleWindow ∧
        (localLength (L0 n) C t)∈paperScaleWindow)
    (hScale : ∀ᶠ n : ℕ in l, (n:ℝ)*p^2=(29/9)*(paperPeriod (d n):ℝ)^2*v n)
    (D : ℕ) (hD : 2*(2*T+1/w)+1≤D) :
    ∀ᶠ n in l,
      let K := (paperPeriod (d n):ℝ)
      let Ls := localLength (L0 n) (K*v n) s
      let Lt := localLength (L0 n) (K*v n) t
      |(n:ℝ)*periodL2Sq (fun x => X n Lt x-X n Ls x)-(58/(9*(L0 n)^2))*pulseOverlap (1/w) s t s t 0|≤
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
  exact actualLocalSource_finite hd g hg tβ htβ h1' hw mesh n p T (L0 n) s t D hT hvn hD
    hV hs hst ht win.1 safe win.2.1 win.2.2 sc

theorem local_actual_window_increment_tendsto {l : Filter ℕ} {w p T s t Lstar : ℝ}
    (hw : 4≤w) (hT : 0≤T) (hs : -T≤s) (hst : s≤t) (ht : t≤T)
    {b d : ℕ→ℕ} {v L0 : ℕ→ℝ} {X : ℕ→ℝ→ℝ→ℝ}
    (hK : Tendsto (fun n => (paperPeriod (d n):ℝ)) l atTop) (hv : Tendsto v l atTop)
    (hSource : ∀ᶠ n in l, ActualSafeLocalSource w p (v n) (b n) (d n) (L0 n) (X n))
    (hWin : ∀ᶠ n in l,
      let C := (paperPeriod (d n):ℝ)*v n
      L0 n∈paperScaleWindow ∧ (localLength (L0 n) C s)∈paperScaleWindow ∧
        (localLength (L0 n) C t)∈paperScaleWindow)
    (hScale : ∀ᶠ n : ℕ in l, (n:ℝ)*p^2=(29/9)*(paperPeriod (d n):ℝ)^2*v n)
    (hLstar : Lstar∈paperScaleWindow) (hL : Tendsto L0 l (𝓝 Lstar)) :
    Tendsto (fun n =>
      let C := (paperPeriod (d n):ℝ)*v n
      (n:ℝ)*periodL2Sq (fun x => X n (localLength (L0 n) C t) x-X n (localLength (L0 n) C s) x))
      l (𝓝 ((58/(9*Lstar^2))*pulseOverlap (1/w) s t s t 0)) := by
  obtain ⟨D,hD⟩ := exists_nat_ge (2*(2*T+1/w)+1)
  have W := local_actual_window_error_eventually hw hT hs hst ht hK hv hSource hWin hScale D hD
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

#print axioms local_actual_window_error_eventually
#print axioms local_actual_window_increment_tendsto
end CenteredCubeSqrt
