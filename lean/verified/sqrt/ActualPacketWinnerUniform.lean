import ActualPacketWinnerLimitAlongDimensions
import CompactSafeUniform
import PacketLambdaContinuity

open MeasureTheory ProbabilityTheory Filter Set CenteredCubeSqrt CubeBrownian CubeSqrtOverlap
open scoped NNReal ENNReal Topology BigOperators
namespace CubeSqrtProbability
set_option maxHeartbeats 1400000

/-- Correctly normalized one-window probability in the actual common
retained-packet source. -/
noncomputable def paperPacketNormalizedProb (p P A : ℝ) (N n dim i : ℕ)
    (X : ℝ → ℝ → ℝ) : ℝ :=
  let v := paperV p n dim
  let h := v/2-2
  let score (j : Fin (N+1)) (z : Fin n → ℝ) :=
    ∑ c, Real.log (1+X (paperPacketLength (paperPeriod dim) v P A i j) (z c))
  √v*Real.exp h*(Measure.pi fun _ : Fin n ↦ unitPeriodLaw).real {z | h < ⨆ j, score j z}

noncomputable def paperPacketBoxGrid (w A : ℝ) (hw : 4 ≤ w) (hA : 0 < A) (N : ℕ)
    (j : Fin (N+1)) : Lp ℝ 2 (volume : Measure ℝ) :=
  centeredBoxNodeL2 (1/w) ((j:ℝ)*A) (one_div_pos.mpr (by linarith)) (by positivity)

noncomputable def paperPacketLambda (L : ℝ) : ℝ≥0 := (58/(9*L^2):ℝ).toNNReal

/-- Paperwinner (fixed finite box-smoothed node grid), uniform over every
retained safe packet and all sufficiently large actual integer dimensions.
The reference finite Gaussian span is constructed internally. -/
theorem actual_packet_winner_uniform
    {p w P A : ℝ} (hp : 0 < p) (hw : 4 ≤ w) (hA : 0 < A) (hSpacing : 1/w ≤ A)
    {N : ℕ} {b d : ℕ → ℕ} {R : ℕ → Finset ℕ} {X : ℕ → ℝ → ℝ → ℝ}
    (hK : Tendsto (fun n ↦ (paperPeriod (d n):ℝ)) atTop atTop)
    (hv : Tendsto (fun n ↦ paperV p n (d n)) atTop atTop)
    (hAmpV : Tendsto (fun n ↦ (7*|p|/(paperPeriod (d n):ℝ))*paperV p n (d n)) atTop (𝓝 0))
    (hv2 : Tendsto (fun n : ℕ ↦ (paperV p n (d n))^2/(n:ℝ)) atTop (𝓝 0))
    (hData : ∀ᶠ n in atTop,
      let v := paperV p n (d n)
      let K := (paperPeriod (d n):ℝ)
      let B := (2:ℝ)^(b n)
      let M := paperMeshM v
      let r := paperKernelRelError B K (paperAtomicCrossSmoothing w K B v M) M
      v < 144*Real.log (n:ℝ) ∧ v*r ≤ 2/w ∧
      CertifiedActualFamily p w P A n (b n) (d n) N (R n) (X n))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ i ∈ R n,
      |paperPacketNormalizedProb p P A N n (d n) i (X n) -
        φ 0*canonicalFiniteGridExp (paperPacketBoxGrid w A hw hA N)
          (paperPacketLambda (paperPacketLength (paperPeriod (d n)) (paperV p n (d n)) P A i 0))| < ε := by
  let H := paperPacketBoxGrid w A hw hA N
  let L (n i : ℕ) := paperPacketLength (paperPeriod (d n)) (paperV p n (d n)) P A i 0
  let f (n i : ℕ) := paperPacketNormalizedProb p P A N n (d n) i (X n)
  let g (n i : ℕ) := φ 0*canonicalFiniteGridExp H (paperPacketLambda (L n i))
  let safe (n i : ℕ) := i∈R n ∧ CertifiedActualFamily p w P A n (b n) (d n) N (R n) (X n)
  have hparam (n i : ℕ) (hs : safe n i) : L n i∈paperScaleWindow := by
    obtain ⟨_,_,_,_,_,_,_,hp,_,_,_⟩ := hs.2
    exact (hp i hs.1).2.1
  have hC : IsCompact paperScaleWindow := isCompact_Icc
  have hSeq (m i : ℕ → ℕ) (hm : Tendsto m atTop atTop) (hs : ∀ n, safe (m n) (i n))
      (y : ℝ) (hy : y∈paperScaleWindow) (hL : Tendsto (fun n ↦ L (m n) (i n)) atTop (𝓝 y)) :
      Tendsto (fun n ↦ f (m n) (i n)-g (m n) (i n)) atTop (𝓝 0) := by
    have hi : ∀ᶠ n in atTop, i n ∈ R (m n) :=
      Eventually.of_forall fun n ↦ (hs n).1
    have hf : Tendsto (fun n ↦ f (m n) (i n)) atTop
      (𝓝 (φ 0*canonicalFiniteGridExp H (paperPacketLambda y))) :=
      actual_packet_winner_limit_along_anchor_dimensions (P := P) hp hw hA hSpacing m hm
        (N := N) (b := b) (d := d) (i := i) (R := R) (X := X)
        (hK.comp hm) (hv.comp hm) (hAmpV.comp hm) (hv2.comp hm) (hm.eventually hData)
        hi (Lstar := y) hy hL
    have hy0 : 0 < y := by linarith [hy.1]
    have hg : Tendsto (fun n ↦ g (m n) (i n)) atTop
      (𝓝 (φ 0*canonicalFiniteGridExp H (paperPacketLambda y))) :=
      (packet_ref_scale_tendsto H (fun n ↦ L (m n) (i n)) hy0 hL).const_mul (φ 0)
    simpa only [sub_self] using hf.sub hg
  have hu := uniform_of_compact_parameter_sequential paperScaleWindow hC safe L
    (fun n i ↦ f n i-g n i) hparam hSeq ε hε
  filter_upwards [hu,hData] with n hn hd i hi
  exact hn i ⟨hi,hd.2.2⟩

end CubeSqrtProbability
#print axioms CubeSqrtProbability.actual_packet_winner_uniform
