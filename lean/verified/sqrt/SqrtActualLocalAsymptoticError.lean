import SqrtActualLocalScalarBudget
import SqrtPaperKernelChoice

namespace CenteredCubeSqrt
open Set Filter MeasureTheory
open scoped Topology BigOperators
set_option maxHeartbeats 700000
set_option synthInstance.maxHeartbeats 20000
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem actualLocalSource_finite {b d : ℕ} [NeZero (2^d-1)]
    (hd : 0<d) (g : (LabelField d)ˣ) (hg : orderOf g=2^d-1) (tβ : Fin b→LabelField d)
    (htβ : LinearIndependent (ZMod 2) tβ)
    (h1' : (phaseState hd g hg 1 : LabelField d) ∉ labelRatioSet tβ)
    {w v : ℝ} (hw : 4≤w) (hM : PaperMeshParameters w v b d)
    (n : ℕ) (p T L0 s t : ℝ) (D : ℕ) (hT : 0≤T)
    (hV : 2*T+1/w<v) (hD : 2*(2*T+1/w)+1≤D)
    (hm : (T+(1/w)/2)/((paperPeriod d:ℝ)*v)<1/4)
    (hs : -T≤s) (hst : s≤t) (ht : t≤T)
    (hL0 : L0∈paperScaleWindow)
    (hSafe : actualSafeLifts hd g hg tβ L0)
    (hLs : localLength L0 ((paperPeriod d:ℝ)*v) s∈paperScaleWindow)
    (hLt : localLength L0 ((paperPeriod d:ℝ)*v) t∈paperScaleWindow)
    (hscale : (n:ℝ)*p^2=(29/9)*(paperPeriod d:ℝ)^2*v) :
    let K := (paperPeriod d:ℝ)
    let f := ordinalPhaseLabel hd g hg tβ
    let X := actualWindowPerturbation f (paperMeshM v) p (paperMeshDelta w K v)
    let Ls := localLength L0 (K*v) s
    let Lt := localLength L0 (K*v) t
    |(n:ℝ)*periodL2Sq (fun x => X Lt x-X Ls x)-(58/(9*L0^2))*pulseOverlap (1/w) s t s t 0|≤
      actualLocalMainError ((2:ℝ)^b) K v (1/w) T s t D := by
  let K := (paperPeriod d:ℝ)
  have hKnat : 2≤paperPeriod d := by have := hM.period_lower; omega
  have hKr : 0<K := by dsimp [K]; exact_mod_cast (show 0<paperPeriod d by omega)
  have hwp : 0<w := by linarith
  have he : 0<1/w := by positivity
  have he4 : 1/w≤1/4 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hw
  have hv : 0<v := by linarith [hM.v_ge_four]
  have hBv : ((2^b:ℕ):ℝ)≤2*v := by
    push_cast
    exact hM.label_upper.le
  have h0 : 1≤L0 := by linarith [hL0.1]
  have h0s : 1≤localLength L0 (K*v) s := by linarith [hLs.1]
  have h0t : 1≤localLength L0 (K*v) t := by linarith [hLt.1]
  have h1 : (phaseState hd g hg 1 : LabelField d) ≠ 1 := by
    rw [(cyclic_short_shift_values hd g hg).1]
    exact manuscriptShortShifts_ne_one (by rw [hg]; unfold paperPeriod at hKnat; have := hM.period_lower; unfold paperPeriod at this; omega) 0
  have hsafe := actualSafeLifts_regular_coarse hd g hg hM.period_lower hL0 hSafe
  let _ : NeZero (2^b*(2^d-1)) := ⟨Nat.mul_ne_zero (pow_ne_zero _ (by decide)) (NeZero.ne _)⟩
  have H := actual_local_variance_finite hd g hg htβ hM.label_rank hKnat h1 h1'
    (paperMeshM v) (n:=n) (p:=p) (v:=v) (eps:=1/w) (T:=T) (L0:=L0) (s:=s) (t:=t) (D:=D)
    (by positivity) hscale hv he he4 hT hV hBv hD hm hs hst ht h0 h0s h0t hsafe
  have hδ : (1/w)/(K*v)=paperMeshDelta w K v := by
    unfold paperMeshDelta
    rw [div_div]; ring
  have eqB : ((2^b:ℕ):ℝ)=(2:ℝ)^b := by norm_cast
  dsimp only at H ⊢
  rw [show (((2^d-1:ℕ):ℝ))=(paperPeriod d:ℝ) by rfl, hδ,eqB] at H
  exact H

#print axioms actualLocalSource_finite
end CenteredCubeSqrt
