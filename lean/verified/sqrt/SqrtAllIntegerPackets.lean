import SqrtActualPacketCountLimits

namespace CenteredCubeSqrt
open Set Filter Finset CubeSqrtOverlap MvPolynomial
open scoped Topology BigOperators
set_option maxHeartbeats 3000000
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

def ActualPacketChoice (w v P A : ℝ) (b d N : ℕ) (R : Finset ℕ) : Prop :=
  let K := (paperPeriod d:ℝ)
  let raw := Finset.range (rawPacketCount (K*v/18) ((N:ℝ)*A) P)
  PaperMeshParameters w v b d ∧
  R ⊆ raw ∧
  (((raw \ R).card):ℝ)≤((N:ℝ)+1)*(4*v^2)*(2*v/P+1) ∧
  ∃ (hd : 0<d) (hK : NeZero (2^d-1)) (g : (LabelField d)ˣ)
    (hg : orderOf g=2^d-1) (t : Fin b→LabelField d),
    LinearIndependent (ZMod 2) t ∧
    (phaseState hd g hg 1 : LabelField d) ∉ labelRatioSet t ∧
    R=@actualRetainedPackets b d hK hd g hg t v P A N ∧
    (∀ i∈R, ∀ a : Fin (N+1), paperPacketLength K v P A i a ∈ paperScaleWindow ∧
      actualSafeLifts hd g hg t (paperPacketLength K v P A i a)) ∧
    (∀ L J : ℝ, L∈paperScaleWindow → J∈paperScaleWindow →
      actualSafeLifts hd g hg t L → actualSafeLifts hd g hg t J →
      @ActualPaperKernelConclusions b d hK hd g hg t w v L J)

theorem actualPacketChoice_exists {w v P A : ℝ} {b d N : ℕ} (hd : 0<d) (hP : 0<P) (hA : 0≤A)
    (hV : (N:ℝ)*A≤(paperPeriod d:ℝ)*v/18)
    (hM : PaperMeshParameters w v b d)
    (hBudget :
      let K := (paperPeriod d:ℝ)
      let B := (2:ℝ)^b
      let M := paperMeshM v
      let E := paperAtomicCrossSmoothing w K B v M
      paperFarRawBudget B K≤21/500 ∧ E≤1/1000 ∧ paperNearBudget B K E≤1/1000 ∧
        19/50≤paperKernelFloor B K E M) :
    ∃ R, ActualPacketChoice w v P A b d N R := by
  classical
  have nz : NeZero (2^d-1) := ⟨by
    have hP : 1≤paperPeriod d := by have := hM.period_lower; omega
    unfold paperPeriod at hP
    omega⟩
  let _ : NeZero (2^d-1) := nz
  obtain ⟨g,hg,t,ht,h0,hp,hadj,hshort⟩ :=
    actual_manuscript_qualified_labels hM.label_ge_two hM.label_budget
  let K := (paperPeriod d:ℝ)
  let R := actualRetainedPackets hd g hg t v P A N
  have hK : 0<K := by
    dsimp [K]
    exact_mod_cast (show 0<paperPeriod d by have := hM.period_lower; omega)
  have hv : 0<v := by linarith [hM.v_ge_four]
  have hmem i := actual_retained_packets_mem hd g hg t v P A N i
  have hshort1 : (phaseState hd g hg 1 : LabelField d) ∉ labelRatioSet t :=
    (cyclicDefects_short_excluded hd g hg h0 hp hshort).1
  refine ⟨R,hM,fun i hi => ((hmem i).1 hi).1,?_,hd,nz,g,hg,t,ht,hshort1,rfl,?_,?_⟩
  · exact actual_retained_packets_deletion_bound hd g hg t h0 hp hv hP hA N
      hM.period_lower hV hM.label_upper
  · intro i hi a
    obtain ⟨r,s⟩ := (hmem i).1 hi
    exact ⟨paper_packet_raw_grid_valid K v P A hK hv hP hA N hV i r a,s a⟩
  · intro L J hL hJ hSL hSJ
    exact actualPaperKernelConclusions_of_label hd g hg t ht h0 hp hadj hshort hM hBudget hL hJ hSL hSJ

theorem paper_all_integer_dimensions_actual_packets {p w A D : ℝ} (hp : 0<p) (hw : 4≤w)
    (hA : 0<A) (hD : 0<D) (N : ℕ) :
    let P := (N:ℝ)*A+D
    ∃ (d b : ℕ→ℕ) (R : ℕ→Finset ℕ),
      (∀ j : ℕ, Tendsto (fun n => (paperPeriod (d n):ℝ)/(paperV p n (d n))^j) atTop atTop) ∧
      (Tendsto (fun n => ((R n).card:ℝ)/(Real.sqrt (paperV p n (d n))*Real.sqrt (n:ℝ)))
        atTop (𝓝 (paperCp p/(18*P)))) ∧
      (Tendsto (fun n => (2*P/((paperPeriod (d n):ℝ)*paperV p n (d n)))*((R n).card:ℝ))
        atTop (𝓝 (1/9))) ∧
      (∀ᶠ n in atTop, (R n).Nonempty ∧
        16*Real.log n≤paperV p n (d n) ∧ paperV p n (d n)<144*Real.log n ∧
        paperV p n (d n+1)<16*Real.log n ∧
        (∀ e : ℕ, 0<e → 16*Real.log n≤paperV p n e → e≤d n) ∧
        ActualPacketChoice w (paperV p n (d n)) P A (b n) (d n) N (R n)) := by
  classical
  let P := (N:ℝ)*A+D
  have hP : 0<P := by unfold P; positivity
  obtain ⟨d,hd⟩ := paper_dyadic_choice_eventually hp
  let v (n : ℕ) := paperV p n (d n)
  let K (n : ℕ) := (paperPeriod (d n):ℝ)
  have hD' : ∀ᶠ n in atTop, 0<d n ∧ 16*Real.log n≤v n ∧ v n<144*Real.log n :=
    hd.mono fun _ H => ⟨H.1,H.2.1,H.2.2.1⟩
  have hv := paper_v_tendsto (v:=v) (hD'.mono fun _ H => H.2.1)
  have hK (j : ℕ) := paper_period_growth_of_choice hp d hD' j
  obtain ⟨b,hb⟩ := paper_binary_mesh_eventually hw v d hv (hK 4)
  have hK0 : Tendsto K atTop atTop := by simpa only [pow_zero,div_one] using hK 0
  have hB := paper_actual_kernel_finite_budgets hw hb hv (hK 4) hK0
  have hz : Tendsto (fun n => K n*v n/18) atTop atTop := by
    refine tendsto_atTop_mono' atTop ?_ (hK0.const_mul_atTop (by norm_num : (0:ℝ)<1/18))
    filter_upwards [hv.eventually_ge_atTop 1,hK0.eventually_ge_atTop 0] with n hn hk
    linarith [mul_le_mul_of_nonneg_left hn hk]
  let W (n : ℕ) (R : Finset ℕ) := ActualPacketChoice w (v n) P A (b n) (d n) N R
  let R (n : ℕ) : Finset ℕ := if h : ∃ r, W n r then h.choose else ∅
  have hR : ∀ᶠ n in atTop, W n (R n) := by
    filter_upwards [hD',hb,hB,hz.eventually_ge_atTop ((N:ℝ)*A)] with n hn hm he hh
    have Y : ∃ r, W n r := actualPacketChoice_exists hn.1 hP hA.le hh hm he
    dsimp only [R]
    rw [dite_eq_left Y]
    exact Y.choose_spec
  have hC := paper_actual_packet_count_limits hp hD' R N hP hA.le
    (hR.mono fun _ H => H.2.1) (hR.mono fun _ H => H.2.2.1)
  refine ⟨d,b,R,hK,hC.1,hC.2.1,?_⟩
  filter_upwards [hC.2.2,hd,hR] with n hE hn hr
  exact ⟨hE,hn.2.1,hn.2.2.1,hn.2.2.2.1,hn.2.2.2.2,hr⟩

#print axioms actualPacketChoice_exists
#print axioms paper_all_integer_dimensions_actual_packets
end CenteredCubeSqrt
