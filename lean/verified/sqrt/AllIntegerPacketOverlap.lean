import PaperPacketFarRate

namespace CenteredCubeSqrt
open MeasureTheory Set Filter MvPolynomial CubeSqrtOverlap Finset
open scoped ProbabilityTheory Interval Topology
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
set_option maxHeartbeats 3000000

noncomputable def paperPairGlobalEnvelope (p P D : ℝ) (N : ℕ) : ℝ :=
  ((N:ℝ)+1)^2 * paperPairGeometricTerm P D * (paperCp p/(18*P))

/-- Uniform over the exact witnesses in the r23 packet certificate; no
choice of a different score law or label family is required for this bound. -/
def ActualPacketGlobalOverlapBound (p w v P A : ℝ) (n b d N : ℕ) (R : Finset ℕ) (C : ℝ) : Prop :=
  let K := (paperPeriod d:ℝ)
  let M := paperMeshM v
  let δ := paperMeshDelta w K v
  ∀ (hd : 0<d) (nz : NeZero (2^d-1)) (g : (LabelField d)ˣ)
    (hg : orderOf g=2^d-1) (t : Fin b→LabelField d),
  letI : NeZero (2^d-1) := nz
  (∀ i∈R, ∀ a : Fin (N+1), paperPacketLength K v P A i a ∈ paperScaleWindow ∧
      actualSafeLifts hd g hg t (paperPacketLength K v P A i a)) →
  (∀ L J : ℝ, L∈paperScaleWindow → J∈paperScaleWindow →
      actualSafeLifts hd g hg t L → actualSafeLifts hd g hg t J →
      ActualPaperKernelConclusions hd g hg t w v L J) →
  let h := v/2-2
  let U := actualPaperPacketEvent (ordinalPhaseLabel hd g hg t) M n N p δ h v P A
  Real.exp h*actualPaperOverlapSum n R U/Real.sqrt (n:ℝ) ≤ C

theorem paper_r23_eventually_global_overlap
    {p w A D : ℝ} (hp : 0<p) (hw : 4≤w) (hA : 0<A) (hD : 0<D) (N : ℕ)
    (d b : ℕ→ℕ) (R : ℕ→Finset ℕ)
    (hGrowth : ∀ j : ℕ, Tendsto (fun n => (paperPeriod (d n):ℝ)/(paperV p n (d n))^j) atTop atTop)
    (hCount : let P := (N:ℝ)*A+D
      Tendsto (fun n => (R n).card/(Real.sqrt (paperV p n (d n))*Real.sqrt (n:ℝ)))
        atTop (𝓝 (paperCp p/(18*P))))
    (hChoice : ∀ᶠ n in atTop, (R n).Nonempty ∧
        16*Real.log n≤paperV p n (d n) ∧ paperV p n (d n)<144*Real.log n ∧
        paperV p n (d n+1)<16*Real.log n ∧
        (∀ e : ℕ, 0<e → 16*Real.log n≤paperV p n e → e≤d n) ∧
        ActualPacketChoice w (paperV p n (d n)) ((N:ℝ)*A+D) A (b n) (d n) N (R n))
    (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ n in atTop, let P := (N:ℝ)*A+D
      ActualPacketGlobalOverlapBound p w (paperV p n (d n)) P A n (b n) (d n) N (R n)
        (paperPairGlobalEnvelope p P D N+ε) := by
  let P := (N:ℝ)*A+D
  let T := (N:ℝ)*A
  let v (n : ℕ) := paperV p n (d n)
  let u (n : ℕ) := Real.sqrt (v n)
  let K (n : ℕ) := (paperPeriod (d n):ℝ)
  let B₀ (n : ℕ) : ℝ := rawPacketCount (K n*v n/18) T P
  let J := paperCp p/(18*P)
  let S := ((N:ℝ)+1)^2
  let G := paperPairGeometricTerm P D
  let Far (n : ℕ) := B₀ n*(actualPairPrefactor*Real.exp (-v n/25))
  let Rate (n : ℕ) := S*(G+Far n)*((R n).card/(u n*Real.sqrt (n:ℝ)))
  have hP : 0<P := by unfold P; positivity
  have hT : 0≤T := by unfold T; positivity
  have hd : ∀ᶠ n in atTop, 0<d n ∧ 16*Real.log n≤v n ∧ v n<144*Real.log n := by
    filter_upwards [hChoice] with n H
    obtain ⟨_,hLo,hHi,_,_,hm,_,_,hd,_,_,_,_,_,_,_⟩ := H
    exact ⟨hd,hLo,hHi⟩
  have hv := paper_v_tendsto (v:=v) (hd.mono fun _ H => H.2.1)
  have hMesh : ∀ᶠ n in atTop, PaperMeshParameters w (v n) (b n) (d n) :=
    hChoice.mono fun _ H => H.2.2.2.2.2.1
  have hK0 : Tendsto K atTop atTop := by simpa only [pow_zero,div_one] using hGrowth 0
  have hK1 : Tendsto (fun n => K n/v n) atTop atTop := by simpa only [pow_one] using hGrowth 1
  have hScalar := actual_pair_dimension_conditions hp hw hMesh hv (hGrowth 4) hK1 hK0
  have hBudget := paper_actual_kernel_finite_budgets hw hMesh hv (hGrowth 4) hK0
  have hRoom : ∀ᶠ n in atTop, T≤K n*v n/18 := by
    have hK' := (hK0.const_mul_atTop (by norm_num : (0:ℝ)<1/18)).eventually_ge_atTop T
    filter_upwards [hK',hK0.eventually_ge_atTop 0,hv.eventually_ge_atTop 1] with n hK' hk hv
    change T≤(1/18)*K n at hK'
    linarith only [hK',mul_le_mul_of_nonneg_left hv hk]
  have hFar : Tendsto Far atTop (𝓝 0) := paper_all_integer_far_packet_rate hp hd hP hT
  have hCount : Tendsto (fun n => (R n).card/(u n*Real.sqrt (n:ℝ))) atTop (𝓝 J) := hCount
  have hRate : Tendsto Rate atTop (𝓝 (S*G*J)) := by
    have q := ((hFar.const_add G).const_mul S).mul hCount
    simpa only [add_zero] using q
  have hLT : S*G*J<S*G*J+ε := by linarith
  filter_upwards [hChoice,hScalar,hBudget,hRoom,eventually_gt_atTop (0:ℕ),hRate.eventually_lt_const hLT]
    with n hc hs hb hr hn hRate
  change ActualPacketGlobalOverlapBound p w (v n) P A n (b n) (d n) N (R n) (S*G*J+ε)
  dsimp only [ActualPacketGlobalOverlapBound]
  intro hd nz g hg t
  letI : NeZero (2^d n-1) := nz
  intro hSafeNodes hG
  have H := paper_actual_packet_overlap_choice hp hA hD N hn (R n) hc.1 hd g hg t
    hc.2.2.2.2.2.1 hc.2.2.2.2.2.2.1 hr hSafeNodes hG hb.2.2.2 hs
  let h := v n/2-2
  let U := actualPaperPacketEvent (ordinalPhaseLabel hd g hg t) (paperMeshM (v n)) n N p
    (paperMeshDelta w (K n) (v n)) h (v n) P A
  let μ := Real.exp h*actualPaperOverlapSum n (R n) U
  let Jn := ((R n).card:ℝ)
  let q := Real.sqrt (n:ℝ)
  have Jp : 0<Jn := by unfold Jn; exact_mod_cast hc.1.card_pos
  have q0 : 0<q := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have u0 : 0<u n := by
     apply Real.sqrt_pos.2
     linarith [hc.2.2.2.2.2.1.v_ge_four]
  have E0 : u n*μ/Jn≤S*(G+Far n) := by convert H using 1 <;> unfold μ <;> ring
  have E := mul_le_mul_of_nonneg_right E0 (show 0≤Jn/(u n*q) by positivity)
  have e : u n*μ/Jn*(Jn/(u n*q))=μ/q := by field_simp [Jp.ne',u0.ne',q0.ne']
  rw [e] at E
  change μ/q ≤ S*G*J+ε
  exact E.trans (by exact hRate.le)

#print axioms paper_r23_eventually_global_overlap
end CenteredCubeSqrt
