import ActualAmplitudeScale
import TrueFixedWindowMainTermAlongDimensions
import ActualLocalAlongDimensions
import ActualWindowLaw
import CanonicalFiniteGrid
import SqrtCertifiedActualSource
import SqrtActualPacketLocalLimit
import CenteredBoxActualPulse
import BoxNodeNondegenerate

open MeasureTheory ProbabilityTheory Filter Set CenteredCubeSqrt CubeBrownian CubeSqrtOverlap
open scoped NNReal ENNReal Topology BigOperators Interval
namespace CubeSqrtProbability

set_option maxHeartbeats 3000000

/-- The genuine paper packet at any sequence of retained safe anchors
whose lengths converge. The finite-node formula contains the manuscript's
actual one-period iid probability, with threshold v/2−2. -/
theorem actual_packet_winner_limit_along_anchor_dimensions
    {p w P A : ℝ} (hp : 0 < p) (hw : 4 ≤ w) (hA : 0 < A) (hSpacing : 1/w ≤ A)
    (dim : ℕ → ℕ) (hDim : Tendsto dim atTop atTop)
    {N : ℕ} {b d i : ℕ → ℕ} {R : ℕ → Finset ℕ} {X : ℕ → ℝ → ℝ → ℝ}
    (hK : Tendsto (fun n ↦ (paperPeriod (d (dim n)):ℝ)) atTop atTop)
    (hv : Tendsto (fun n ↦ paperV p (dim n) (d (dim n))) atTop atTop)
    (hAmpV : Tendsto (fun n ↦ (7*|p|/(paperPeriod (d (dim n)):ℝ))*paperV p (dim n) (d (dim n))) atTop (𝓝 0))
    (hv2 : Tendsto (fun n : ℕ ↦ (paperV p (dim n) (d (dim n)))^2/(dim n:ℝ)) atTop (𝓝 0))
    (hData : ∀ᶠ n in atTop,
      let v := paperV p (dim n) (d (dim n))
      let K := (paperPeriod (d (dim n)):ℝ)
      let B := (2:ℝ)^(b (dim n))
      let M := paperMeshM v
      let r := paperKernelRelError B K (paperAtomicCrossSmoothing w K B v M) M
      v < 144*Real.log (dim n:ℝ) ∧ v*r ≤ 2/w ∧
      CertifiedActualFamily p w P A (dim n) (b (dim n)) (d (dim n)) N (R (dim n)) (X (dim n)))
    (hi : ∀ᶠ n in atTop, i n ∈ R (dim n))
    {Lstar : ℝ} (hLstar : Lstar∈paperScaleWindow)
    (hL : Tendsto (fun n ↦ paperPacketLength (paperPeriod (d (dim n))) (paperV p (dim n) (d (dim n))) P A (i n) 0)
      atTop (𝓝 Lstar)) :
    let v n := paperV p (dim n) (d (dim n))
    let h n := v n/2-2
    let score (n : ℕ) (j : Fin (N+1)) (z : Fin (dim n) → ℝ) :=
      ∑ c, Real.log (1+X (dim n) (paperPacketLength (paperPeriod (d (dim n))) (v n) P A (i n) j) (z c))
    let lam := (58/(9*Lstar^2):ℝ).toNNReal
    let H (j : Fin (N+1)) := centeredBoxNodeL2 (1/w) ((j:ℝ)*A)
      (one_div_pos.mpr (by linarith)) (by positivity)
    Tendsto (fun n ↦ √(v n)*Real.exp (h n)*
      (Measure.pi fun _ : Fin (dim n) ↦ unitPeriodLaw).real {z | h n < ⨆ j, score n j z})
      atTop (𝓝 (φ 0*canonicalFiniteGridExp H lam)) := by
  classical
  dsimp only
  let K n := (paperPeriod (d (dim n)):ℝ)
  let v n := paperV p (dim n) (d (dim n))
  let h n := v n/2-2
  let amp n := 7*|p|/K n
  let L (n : ℕ) (j : Fin (N+1)) := paperPacketLength (K n) (v n) P A (i n) j
  let G (n : ℕ) (j : Fin (N+1)) := X (dim n) (L n j)
  have hw0 : 0<w := by linarith
  have hε : 0 < 1/w := one_div_pos.mpr hw0
  let lam : ℝ≥0 := (58/(9*Lstar^2):ℝ).toNNReal
  have hLs : 0<Lstar := by linarith [hLstar.1]
  have hlam : 0 < (58/(9*Lstar^2):ℝ) := by positivity
  have hlam0 : 0<lam := Real.toNNReal_pos.mpr hlam
  have hlameq : (lam:ℝ)=58/(9*Lstar^2) := Real.coe_toNNReal _ hlam.le
  let H (j : Fin (N+1)) := centeredBoxNodeL2 (1/w) ((j:ℝ)*A) hε (by positivity)
  have hHinj : Function.Injective H := by
    intro j t he
    by_contra hne
    have hSep (a c : Fin (N+1)) (hac : a<c) : (a:ℝ)*A+1/w ≤ (c:ℝ)*A := by
      have hNat : (a:ℕ)+1 ≤ (c:ℕ) := hac
      have hReal : (a:ℝ)+1 ≤ (c:ℝ) := by exact_mod_cast hNat
      nlinarith
    rcases lt_or_gt_of_ne hne with hl | hr
    · exact (centeredBoxNodeL2_ne_of_separated hε (show 0 ≤ (j:ℝ)*A by positivity) (show 0 ≤ (t:ℝ)*A by positivity) (hSep j t hl)) he
    · exact (centeredBoxNodeL2_ne_of_separated hε (show 0 ≤ (t:ℝ)*A by positivity) (show 0 ≤ (j:ℝ)*A by positivity) (hSep t j hr)) he.symm
  have hAmp : Tendsto amp atTop (𝓝 0) := by
    simpa [amp,div_eq_mul_inv] using (tendsto_inv_atTop_zero.comp hK).const_mul (7*|p|)
  have hSource : ∀ᶠ n in atTop, ∀ j∈R (dim n),
      let L0 := paperPacketLength (K n) (v n) P A j 0
      ActualSafeLocalSource w p (v n) (b (dim n)) (d (dim n)) L0 (X (dim n)) ∧ L0∈paperScaleWindow ∧
        ∀ z : Fin (N+1), localLength L0 (K n*v n) ((z:ℝ)*A) ∈ paperScaleWindow :=
    hData.mono fun n hn ↦ by
      obtain ⟨_,_,_,_,_,_,_,hpacket,_,_,_⟩ := hn.2.2
      exact hpacket
  have hFacts : ∀ᶠ n : ℕ in atTop, 0<d (dim n) ∧ 0<K n ∧ 0<v n ∧ v n ≤ 144*Real.log (dim n:ℝ) ∧
      0 ≤ amp n ∧ amp n ≤ 1/2 ∧ ∀ j,
        Continuous (G n j) ∧ (∫ x, G n j x ∂unitPeriodLaw)=0 ∧
        (∀ x, |G n j x| ≤ amp n) ∧ |(dim n:ℝ)*rawSq unitPeriodLaw (G n j)-v n| ≤ 2/w := by
    filter_upwards [hData,hi,hK.eventually_gt_atTop 0,hv.eventually_gt_atTop 0,
      hAmp.eventually_lt_const (show (0:ℝ)<1/2 by norm_num)] with n hn hi hnK hnv hsmall
    obtain ⟨hd,_,g,hg,t,_,_,_,hGood,_,hNodes⟩ := hn.2.2
    refine ⟨hd,hnK,hnv,hn.1.le,by dsimp [amp]; positivity,hsmall.le,?_⟩
    intro j
    obtain ⟨hl,hs⟩ := hNodes (i n) hi j
    obtain ⟨hc,hz,hb,hq⟩ := hGood (L n j) hl hs
    exact ⟨hc,by rwa [unitPeriod_integral],hb,by rw [actual_window_raw_sq]; exact hq.trans hn.2.1⟩
  obtain ⟨n0,hn0⟩ := Filter.eventually_atTop.mp hFacts
  let da (j : Fin (N+1)) (n : ℕ) : ℝ → ℝ := if n0≤n then G n j else 0
  let a (n : ℕ) := if n0≤n then amp n else 0
  have hda (n : ℕ) (hn : n0≤n) (j : Fin (N+1)) : da j n=G n j := if_pos hn
  have hAd (n : ℕ) (hn : n0≤n) : a n=amp n := if_pos hn
  have hdX j n : Measurable (da j n) := by
    by_cases hn : n0≤n
    · rw [hda _ hn]; exact ((hn0 n hn).2.2.2.2.2.2 j).1.measurable
    · change Measurable (if n0 ≤ n then G n j else (0 : ℝ → ℝ))
      rw [if_neg hn]
      exact (show Measurable (fun _ : ℝ ↦ (0:ℝ)) from measurable_const)
  have ha0 n : 0≤a n := by
    by_cases hn : n0≤n
    · rw [hAd _ hn]; exact (hn0 n hn).2.2.2.2.1
    · simp [a,hn]
  have ha n : a n≤1/2 := by
    by_cases hn : n0≤n
    · rw [hAd _ hn]; exact (hn0 n hn).2.2.2.2.2.1
    · simp [a,hn]
  have hb j n x : |da j n x|≤a n := by
    by_cases hn : n0≤n
    · rw [hda _ hn,hAd _ hn]; exact ((hn0 n hn).2.2.2.2.2.2 j).2.2.1 x
    · simp [da,a,hn]
  have hZero j n : (∫ x, da j n x ∂unitPeriodLaw)=0 := by
    by_cases hn : n0≤n
    · rw [hda _ hn]; exact ((hn0 n hn).2.2.2.2.2.2 j).2.1
    · simp [da,hn]
  have haL : Tendsto a atTop (𝓝 0) := hAmp.congr' ((eventually_ge_atTop n0).mono fun n hn ↦ (hAd _ hn).symm)
  have hAV : Tendsto (fun n ↦ a n*v n) atTop (𝓝 0) :=
    hAmpV.congr' ((eventually_ge_atTop n0).mono fun n hn ↦ by change amp n*v n=a n*v n; rw [hAd _ hn])
  have hq : ∀ᶠ n : ℕ in atTop, ∀ j, |(dim n:ℝ)*rawSq unitPeriodLaw (da j n)-v n|≤2/w := by
    filter_upwards [eventually_ge_atTop n0] with n hn j
    rw [hda _ hn]
    exact ((hn0 n hn).2.2.2.2.2.2 j).2.2.2
  have hRates (j : Fin (N+1)) := actual_q_rate_transfer_dims dim (q := fun n ↦ (dim n:ℝ)*rawSq unitPeriodLaw (da j n))
    hv hAV hv2 (2/w) (by positivity) (hq.mono fun n hn ↦ hn j)
  have hSmall (j : Fin (N+1)) : Tendsto (fun n : ℕ ↦ (dim n:ℝ)*a n*rawSq unitPeriodLaw (da j n)) atTop (𝓝 0) := by
    simpa [mul_left_comm,mul_assoc] using (hRates j).2.1
  have hSqZ (j : Fin (N+1)) : Tendsto (fun n ↦ rawSq unitPeriodLaw (da j n)) atTop (𝓝 0) := by
    refine (hRates j).2.2.1.congr' ?_
    filter_upwards [hDim.eventually_ge_atTop (1:ℕ)] with n hn
    have hn' : (dim n:ℝ)≠0 := by exact_mod_cast (show dim n≠0 by omega)
    field_simp
  have hVlog : ∀ᶠ n : ℕ in atTop, 0≤v n ∧ v n≤144*Real.log (dim n:ℝ) :=
    hFacts.mono fun n hn ↦ ⟨hn.2.2.1.le,hn.2.2.2.1⟩
  have hampr : ∀ᶠ n : ℕ in atTop, 8*a n≤112*(√(v n)*(dim n:ℝ)^(-(1/2:ℝ))) := by
    filter_upwards [hFacts,eventually_ge_atTop n0,hDim.eventually_ge_atTop (1:ℕ)] with n hn hn0' hn1
    have hn' : 0<(dim n:ℝ) := by exact_mod_cast (show 0<dim n by omega)
    have hK' := hn.2.1
    have hv' := hn.2.2.1
    rw [hAd _ hn0']
    exact actual_amplitude_scale hn' hK' hv'.le hp.le (actual_v_exact_scale p (n:=dim n) hn.1)
  have hDist (j t : Fin (N+1)) : Tendsto (fun n : ℕ ↦ (dim n:ℝ)*rawSq unitPeriodLaw (fun x ↦ da j n x-da t n x))
      atTop (𝓝 ((lam:ℝ)*‖H j-H t‖^2)) := by
    have ordered (l r : Fin (N+1)) (hlr : l≤r) :
        Tendsto (fun n : ℕ ↦ (dim n:ℝ)*rawSq unitPeriodLaw (fun x ↦ da r n x-da l n x))
          atTop (𝓝 ((lam:ℝ)*‖H r-H l‖^2)) := by
      have hl0 : 0≤(l:ℝ)*A := by positivity
      have hr : (l:ℝ)*A≤(r:ℝ)*A := mul_le_mul_of_nonneg_right (by exact_mod_cast hlr) hA.le
      have bx := centeredBoxNodeL2_sq_eq_actualPulse hε hl0 hr
      have hP := (packet_actual_local_limit_along_anchor_dims dim hw hA.le hlr hK hv hSource hi hLstar hL).1
      rw [hlameq,show ‖H r-H l‖^2 = _ from bx]
      refine hP.congr' ?_
      filter_upwards [eventually_ge_atTop n0] with n hn
      rw [hda _ hn,hda _ hn,actual_window_raw_sq]
    rcases le_total t j with ht | hj
    · exact ordered _ _ ht
    · rw [norm_sub_rev]
      apply (ordered _ _ hj).congr
      intro n
      congr 1
      unfold rawSq
      congr 1
      funext x
      ring
  let Es := gridSpan H
  letI : MeasurableSpace Es := borel _
  letI : BorelSpace Es := ⟨rfl⟩
  let W := pairedSpanIsonormal Es
  let ν := stdGaussian Es
  let nodes := gridSpanNode H
  have hNodeInj : Function.Injective nodes := fun _ _ he ↦ hHinj (congrArg Subtype.val he)
  have hNodeDist (j t : Fin (N+1)) : Tendsto
      (fun n : ℕ ↦ (dim n:ℝ)*rawSq unitPeriodLaw (fun x ↦ da j n x-da t n x))
      atTop (𝓝 ((lam:ℝ)*‖nodes j-nodes t‖^2)) := hDist j t
  have hMain := true_fixed_window_exceedance_main_term_along_dimensions unitPeriodLaw (show 0<N+1 by omega) dim hDim
    da a v h hdX ha0 ha hb hZero haL hv hSmall hSqZ (fun j ↦ (hRates j).2.2.2) (2/w) hq
    2 (Eventually.of_forall fun n ↦ by dsimp [h]; rw [show v n/2-(v n/2-2)=2 by ring]; norm_num)
    144 (by norm_num) hVlog 112 (by norm_num) hampr ν W (fun x ↦ measurable_pairedSpanIsonormal x) (fun x ↦ pairedSpanIsonormal_hasLaw x)
    hlam0 nodes hNodeInj hNodeDist
  refine hMain.congr' ?_
  filter_upwards [eventually_ge_atTop n0] with n hn
  simp_rw [hda _ hn]
  rfl

end CubeSqrtProbability
#print axioms CubeSqrtProbability.actual_packet_winner_limit_along_anchor_dimensions
