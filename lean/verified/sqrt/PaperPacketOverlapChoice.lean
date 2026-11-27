import ActualPacketOverlapEndpoint
import ActualPairScalarRates

namespace CenteredCubeSqrt
open MeasureTheory ProbabilityTheory Set Filter MvPolynomial CubeBrownian CubeSqrtProbability CubeSqrtOverlap Finset
open scoped ProbabilityTheory Interval Topology
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
set_option maxHeartbeats 2500000

noncomputable def paperPairGeometryC : ℝ := 174/121/8

noncomputable def paperPairGeometricTerm (P D : ℝ) : ℝ :=
  actualPairPrefactor*Real.exp (1/4)*Real.exp (-paperPairGeometryC*D)/
    (1-Real.exp (-paperPairGeometryC*P))

noncomputable def actualPaperPacketEvent {B K : ℕ} [NeZero K] (f : ZMod K → Fin B)
    (M n N : ℕ) (p δ h v P A : ℝ) (i : ℕ) : Set (Fin n → ℝ) :=
  ⋃ a : Fin (N+1), actualPaperScaleEvent f M n p δ h (paperPacketLength (K:ℝ) v P A i a.1)

noncomputable def actualPaperOverlapSum (n : ℕ) (R : Finset ℕ) (U : ℕ → Set (Fin n → ℝ)) : ℝ :=
  ∑ i ∈ R, ∑ j ∈ R.filter (fun j => i<j), (actualPaperProductLaw n).real (U i∩U j)

theorem paperV_eq_pair_scale (p : ℝ) (n d : ℕ) :
    paperV p n d=(n:ℝ)*(p/(paperPeriod d:ℝ))^2*(9/29) := by
  unfold paperV
  ring

theorem paper_actual_packet_overlap_choice
    {p w A D : ℝ} (hp : 0<p) (hA : 0<A) (hD : 0<D) (N : ℕ) {n b d : ℕ} (hn : 0<n)
    (R : Finset ℕ) (hR : R.Nonempty)
    (hd : 0<d) [NeZero (2^d-1)]
    (g : (LabelField d)ˣ) (hg : orderOf g=2^d-1) (t : Fin b → LabelField d)
    (hMesh : PaperMeshParameters w (paperV p n d) b d)
    (hSub : let K := (paperPeriod d:ℝ); let v := paperV p n d; let P := (N:ℝ)*A+D
      R ⊆ range (rawPacketCount (K*v/18) ((N:ℝ)*A) P))
    (hRoom : (N:ℝ)*A≤(paperPeriod d:ℝ)*paperV p n d/18)
    (hSafeNodes : ∀ i∈R, ∀ a : Fin (N+1),
      let L := paperPacketLength (paperPeriod d:ℝ) (paperV p n d) ((N:ℝ)*A+D) A i a.1
      L∈paperScaleWindow ∧ actualSafeLifts hd g hg t L)
    (hG : ∀ L J : ℝ, L∈paperScaleWindow → J∈paperScaleWindow →
      actualSafeLifts hd g hg t L → actualSafeLifts hd g hg t J →
      ActualPaperKernelConclusions hd g hg t w (paperV p n d) L J)
    (hV : 19/50≤paperKernelFloor ((2:ℝ)^b) (paperPeriod d:ℝ)
       (paperAtomicCrossSmoothing w (paperPeriod d:ℝ) ((2:ℝ)^b) (paperV p n d) (paperMeshM (paperV p n d)))
       (paperMeshM (paperV p n d)))
    (hScalars : let K := (paperPeriod d:ℝ); let v := paperV p n d; let B := (2:ℝ)^b
      let M := paperMeshM v; let δ := paperMeshDelta w K v
      7*p/K≤1/8 ∧ v*actualPairRelativeError B K M δ≤1 ∧
      4*v/5≤(v-1)/(1+7*p/K) ∧ 8*v*actualPairNearError B K M δ≤2) :
    let K := (paperPeriod d:ℝ)
    let v := paperV p n d
    let u := Real.sqrt v
    let h := v/2-2
    let P := (N:ℝ)*A+D
    let M := paperMeshM v
    let δ := paperMeshDelta w K v
    let U := actualPaperPacketEvent (ordinalPhaseLabel hd g hg t) M n N p δ h v P A
    let B₀ := rawPacketCount (K*v/18) ((N:ℝ)*A) P
    u*Real.exp h*actualPaperOverlapSum n R U/(R.card:ℝ) ≤
      ((N:ℝ)+1)^2*(paperPairGeometricTerm P D + (B₀:ℝ)*(actualPairPrefactor*Real.exp (-v/25))) := by
  let K := (paperPeriod d:ℝ)
  let B := (2:ℝ)^b
  let v := paperV p n d
  let M := paperMeshM v
  let δ := paperMeshDelta w K v
  let P := (N:ℝ)*A+D
  let f := ordinalPhaseLabel hd g hg t
  let E := paperAtomicCrossSmoothing w K B v M
  have hK₀ : 0<K := by dsimp [K]; exact_mod_cast (show 0<paperPeriod d by have := hMesh.period_lower; omega)
  have hB₀ : 0<B := by unfold B; positivity
  have hδB : δ<1/((((2^b:ℕ):ℝ))*K) := by
    rw [show ((2^b:ℕ):ℝ)=B by unfold B; norm_cast]
    refine hMesh.delta_small.trans_le ?_
    apply div_le_div_of_nonneg_left (by norm_num) (mul_pos hB₀ hK₀)
    linarith [mul_pos hB₀ hK₀]
  have hP : 0<P := by unfold P; positivity
  have hv : 0<v := by linarith [hMesh.v_ge_four]
  have hN : paperNearBudget B K E=actualPairNearError B K M δ := by
    unfold paperNearBudget E paperAtomicCrossSmoothing actualPairNearError
    ring
  have hRel : paperKernelRelError B K E M=actualPairRelativeError B K M δ := by
    unfold paperKernelRelError E paperAtomicCrossSmoothing paperDiagonalBudget paperPlateauTail actualPairRelativeError
    ring
  have H (L J : ℝ) (hL : L∈paperScaleWindow) (hJ : J∈paperScaleWindow)
      (hSL : actualSafeLifts hd g hg t L) (hSJ : actualSafeLifts hd g hg t J) :
      let τ := K*|J-L|/2
      let κ := actualNormalizedGram f M δ L J
      (0<actualWitnessGram f M δ L L ∧
        |actualWitnessGram f M δ L L/((27/29)*L^2/3)-1|≤actualPairRelativeError B K M δ) ∧
      (0<actualWitnessGram f M δ J J ∧
        |actualWitnessGram f M δ J J/((27/29)*J^2/3)-1|≤actualPairRelativeError B K M δ) ∧
      (τ≤1/8 → (174/121)*τ-8*actualPairNearError B K M δ≤1-κ) ∧
      -(1/2:ℝ)≤κ ∧ (1/8≤τ → 1/5≤1-κ) := by
    have hG := hG L J hL hJ hSL hSJ
    change ((paperKernelFloor B K E M≤actualWitnessGram f M δ L L ∧ _≤paperKernelRelError B K E M) ∧
      (paperKernelFloor B K E M≤actualWitnessGram f M δ J J ∧ _≤paperKernelRelError B K E M) ∧
      (_ → _-8*paperNearBudget B K E≤_) ∧ _ ) at hG
    rw [hRel,hN] at hG
    have hVV : 19/50≤paperKernelFloor B K E M := hV
    refine ⟨⟨(by norm_num : (0:ℝ)<19/50).trans_le (hVV.trans hG.1.1),hG.1.2⟩,
      ⟨(by norm_num : (0:ℝ)<19/50).trans_le (hVV.trans hG.2.1.1),hG.2.1.2⟩,
      hG.2.2.1,hG.2.2.2.2⟩
  refine actual_retained_overlap_from_packet_kernel hd g hg t M hMesh.delta_positive hδB hMesh.period_lower hn hp
    (Real.sqrt_pos.2 hv) (Real.sq_sqrt hv.le) (paperV_eq_pair_scale p n d)
    hScalars.1 hScalars.2.1 hScalars.2.2.1 hScalars.2.2.2
    N P A D hP hA.le hD le_rfl hRoom R hR hSub hSafeNodes ?_
  intro i j hi hj a b'
  exact H _ _ (hSafeNodes i hi a).1 (hSafeNodes j hj b').1 (hSafeNodes i hi a).2 (hSafeNodes j hj b').2

#print axioms paper_actual_packet_overlap_choice
end CenteredCubeSqrt
