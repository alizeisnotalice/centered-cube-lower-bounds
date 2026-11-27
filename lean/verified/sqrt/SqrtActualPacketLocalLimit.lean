import SqrtActualPacketLocal

namespace CenteredCubeSqrt
open Set Filter MeasureTheory CubeSqrtOverlap
open scoped Topology BigOperators
set_option maxHeartbeats 1600000

theorem packet_actual_local_limit_along_anchor {l : Filter ℕ} {w p P A : ℝ}
    (hw : 4≤w) (hA : 0≤A) {N : ℕ} {a c : Fin (N+1)} (hac : a≤c)
    {b d i : ℕ→ℕ} {R : ℕ→Finset ℕ} {X : ℕ→ℝ→ℝ→ℝ}
    (hK : Tendsto (fun n => (paperPeriod (d n):ℝ)) l atTop)
    (hv : Tendsto (fun n => paperV p n (d n)) l atTop)
    (hSource : ∀ᶠ n in l, ∀ j∈R n,
      let K := (paperPeriod (d n):ℝ)
      let v := paperV p n (d n)
      let L0 := paperPacketLength K v P A j 0
      ActualSafeLocalSource w p v (b n) (d n) L0 (X n) ∧ L0∈paperScaleWindow ∧
      ∀ z : Fin (N+1), localLength L0 (K*v) ((z:ℝ)*A)∈paperScaleWindow)
    (hi : ∀ᶠ n in l, i n∈R n) {Lstar : ℝ} (hLstar : Lstar∈paperScaleWindow)
    (hL : Tendsto (fun n => paperPacketLength (paperPeriod (d n)) (paperV p n (d n)) P A (i n) 0)
      l (𝓝 Lstar)) :
    (Tendsto (fun n =>
      let K := (paperPeriod (d n):ℝ)
      let v := paperV p n (d n)
      (n:ℝ)*periodL2Sq (fun x =>
        X n (paperPacketLength K v P A (i n) c) x-X n (paperPacketLength K v P A (i n) a) x))
      l (𝓝 ((58/(9*Lstar^2))*pulseOverlap (1/w) ((a:ℝ)*A) ((c:ℝ)*A) ((a:ℝ)*A) ((c:ℝ)*A) 0))) ∧
    (∃ C : ℝ, ∀ᶠ n in l,
      let K := (paperPeriod (d n):ℝ)
      let v := paperV p n (d n)
      |(n:ℝ)*periodInner (X n (paperPacketLength K v P A (i n) 0))
        (fun x => X n (paperPacketLength K v P A (i n) c) x-X n (paperPacketLength K v P A (i n) a) x)|≤C) := by
  let L0 (n : ℕ) := paperPacketLength (paperPeriod (d n)) (paperV p n (d n)) P A (i n) 0
  let T := (N:ℝ)*A
  let s := (a:ℝ)*A
  let t := (c:ℝ)*A
  let v (n : ℕ) := paperV p n (d n)
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
  have hdata : ∀ᶠ n in l, ActualSafeLocalSource w p (v n) (b n) (d n) (L0 n) (X n) ∧
      (let K := (paperPeriod (d n):ℝ)
       L0 n∈paperScaleWindow ∧ localLength (L0 n) (K*v n) s∈paperScaleWindow ∧
       localLength (L0 n) (K*v n) t∈paperScaleWindow) := by
    filter_upwards [hSource,hi] with n h hR
    have D := h (i n) hR
    exact ⟨D.1,D.2.1,D.2.2 a,D.2.2 c⟩
  have sc : ∀ᶠ n : ℕ in l, (n:ℝ)*p^2=(29/9)*(paperPeriod (d n):ℝ)^2*v n := by
    filter_upwards [hdata] with n h
    obtain ⟨_,hd,_,_,_,_,_⟩ := h.1
    exact actual_v_exact_scale p hd
  have err := local_actual_window_increment_tendsto hw (T:=T) (by dsimp [T]; positivity)
    hs hst ht hK hv (hdata.mono fun _ H => H.1) (hdata.mono fun _ H => H.2) sc hLstar hL
  have bnd := local_actual_baseline_increment_bounded hw (T:=T) (by dsimp [T]; positivity)
    hs hst ht hK hv (hdata.mono fun _ H => H.1) (hdata.mono fun _ H => H.2) sc
  dsimp only [L0,s,t,v] at err bnd
  simp_rw [paper_packet_localLength_eq] at err bnd
  exact ⟨err,bnd⟩

#print axioms packet_actual_local_limit_along_anchor
end CenteredCubeSqrt
