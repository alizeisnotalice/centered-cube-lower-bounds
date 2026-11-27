import SqrtActualLocalAsymptotic
import SqrtActualBaselineIncrement

namespace CenteredCubeSqrt
open Set Filter MeasureTheory
open scoped Topology BigOperators
set_option maxHeartbeats 650000
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem local_actual_baseline_increment_bounded {l : Filter ℕ} {w p T s t : ℝ}
    (hw : 4≤w) (hT : 0≤T) (hs : -T≤s) (hst : s≤t) (ht : t≤T)
    {b d : ℕ→ℕ} {v L0 : ℕ→ℝ} {X : ℕ→ℝ→ℝ→ℝ}
    (hK : Tendsto (fun n => (paperPeriod (d n):ℝ)) l atTop) (hv : Tendsto v l atTop)
    (hSource : ∀ᶠ n in l, ActualSafeLocalSource w p (v n) (b n) (d n) (L0 n) (X n))
    (hWin : ∀ᶠ n in l,
      let C := (paperPeriod (d n):ℝ)*v n
      L0 n∈paperScaleWindow ∧ (localLength (L0 n) C s)∈paperScaleWindow ∧
        (localLength (L0 n) C t)∈paperScaleWindow)
    (hScale : ∀ᶠ n : ℕ in l, (n:ℝ)*p^2=(29/9)*(paperPeriod (d n):ℝ)^2*v n) :
    ∃ C : ℝ, ∀ᶠ n in l,
      let D := (paperPeriod (d n):ℝ)*v n
      let Ls := localLength (L0 n) D s
      let Lt := localLength (L0 n) D t
      |(n:ℝ)*periodInner (X n (L0 n)) (fun x => X n Lt x-X n Ls x)|≤C := by
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
    (by positivity) hKn' (n:=n) (p:=p) (v:=v n) (eps:=1/w) (T:=T) (L0:=L0 n)
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

#print axioms local_actual_baseline_increment_bounded
end CenteredCubeSqrt
