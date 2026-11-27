import SqrtCertifiedActualSource

namespace CenteredCubeSqrt
open Set Filter MeasureTheory CubeSqrtOverlap
open scoped Topology BigOperators Interval
set_option maxHeartbeats 250000
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

def CertifiedActualFamilyWithKernel (p w P A : ℝ) (n b d N : ℕ) (R : Finset ℕ) (X : ℝ→ℝ→ℝ) : Prop :=
  let K := (paperPeriod d:ℝ)
  let v := paperV p n d
  let B := (2:ℝ)^b
  let M := paperMeshM v
  let δ := paperMeshDelta w K v
  let E := paperAtomicCrossSmoothing w K B v M
  ∃ (hd : 0<d) (hK : NeZero (2^d-1)) (g : (LabelField d)ˣ)
    (hg : orderOf g=2^d-1) (t : Fin b→LabelField d),
    X=@actualWindowPerturbation (2^b) (2^d-1) hK
      (@ordinalPhaseLabel b d hd g hg t) M p δ ∧
    PaperMeshParameters w v b d ∧
    (∀ i∈R,
      let L0 := paperPacketLength K v P A i 0
      ActualSafeLocalSource w p v b d L0 X ∧ L0∈paperScaleWindow ∧
        ∀ z : Fin (N+1), localLength L0 (K*v) ((z:ℝ)*A)∈paperScaleWindow) ∧
    (∀ L∈paperScaleWindow, actualSafeLifts hd g hg t L →
      Continuous (X L) ∧ (∫ x in (0:ℝ)..1,X L x)=0 ∧
      (∀ x : ℝ, |X L x|≤7*|p|/K) ∧
      |(n:ℝ)*periodL2Sq (X L)-v|≤v*paperKernelRelError B K E M) ∧
    (∀ L J, L∈paperScaleWindow → J∈paperScaleWindow →
      actualSafeLifts hd g hg t L → actualSafeLifts hd g hg t J →
      let τ := K * |J-L|/2
      let κ := sourceRhoNormalized X L J
      (τ≤1/8 → (174/121)*τ-8*paperNearBudget B K E≤1-κ) ∧
      (1/8≤τ → τ≤1 → 14703/61952-8*paperNearBudget B K E≤1-κ) ∧
      -(1/2:ℝ)≤κ ∧ (1/8≤τ → 1/5≤1-κ)) ∧
    (∀ i∈R, ∀ a : Fin (N+1),
      paperPacketLength K v P A i a∈paperScaleWindow ∧
      actualSafeLifts hd g hg t (paperPacketLength K v P A i a)) ∧
    (∀ L J, L∈paperScaleWindow → J∈paperScaleWindow →
      actualSafeLifts hd g hg t L → actualSafeLifts hd g hg t J →
      @ActualPaperKernelConclusions b d hK hd g hg t w v L J)

theorem CertifiedActualFamilyWithKernel.forget {p w P A : ℝ} {n b d N : ℕ} {R : Finset ℕ}
    {X : ℝ→ℝ→ℝ} (h : CertifiedActualFamilyWithKernel p w P A n b d N R X) :
    CertifiedActualFamily p w P A n b d N R X := by
  unfold CertifiedActualFamilyWithKernel at h
  unfold CertifiedActualFamily
  obtain ⟨hd,hK,g,hg,t,hx,hm,hanchor,hmom,hgap,hnodes,_⟩ := h
  exact ⟨hd,hK,g,hg,t,hx,hm,hanchor,hmom,hgap,hnodes⟩

#print axioms CertifiedActualFamilyWithKernel.forget

theorem certified_actual_family_with_kernel_exists {p w P A : ℝ} (hp : 0<p) {n b d N : ℕ} {R : Finset ℕ}
    (h : ActualPacketChoice w (paperV p n d) P A b d N R) :
    ∃ X, CertifiedActualFamilyWithKernel p w P A n b d N R X := by
  obtain ⟨mesh,_,_,hd,hK,g,hg,t,ht,hshort,_,hNodes,hKernel⟩ := h
  let _ : NeZero (2^d-1) := hK
  let K := (paperPeriod d:ℝ)
  let v := paperV p n d
  let B := (2:ℝ)^b
  let M := paperMeshM v
  let δ := paperMeshDelta w K v
  let E := paperAtomicCrossSmoothing w K B v M
  let f := ordinalPhaseLabel hd g hg t
  let X := actualWindowPerturbation f M p δ
  have hB : 0<(2^b:ℕ) := by positivity
  have hKr : 0<K := by dsimp [K]; exact_mod_cast (show 0<paperPeriod d by have := mesh.period_lower; omega)
  have hK2 : 2≤(2^d-1:ℕ) := by have := mesh.period_lower; unfold paperPeriod at this; omega
  have hδ : 0<δ := mesh.delta_positive
  have hδ' : δ<1/((((2^b:ℕ):ℝ))*K) := by
    have e : ((2^b:ℕ):ℝ)=B := by dsimp [B]; norm_cast
    rw [e]
    refine mesh.delta_small.trans_le ?_
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    nlinarith [show 0<B*K by positivity]
  refine ⟨X,?_⟩
  unfold CertifiedActualFamilyWithKernel
  refine ⟨hd,hK,g,hg,t,rfl,mesh,?_,?_,?_,hNodes,hKernel⟩
  · intro i hi
    have at_zero := hNodes i hi 0
    refine ⟨⟨mesh,hd,hK,g,hg,t,ht,hshort,at_zero.2,rfl⟩,at_zero.1,?_⟩
    intro a
    rw [paper_packet_localLength_eq]
    exact (hNodes i hi a).1
  · intro L hL hS
    have hL' : 1≤L := by linarith [hL.1]
    have hL0 : 0<L := by linarith
    have C := hKernel L L hL hL hS hS
    exact ⟨actualWindowPerturbation_continuous_length_fixed f M p hδ hL0,
      actualWindowPerturbation_integral_zero f M p hB hK2 hδ hδ' hL0,
      actual_source_uniform_amplitude f M hB hK2 hδ hδ' hL',
      actual_safe_q_relative_bound hd g hg t w p n hL mesh C⟩
  · intro L J hL hJ hSL hSJ
    have hL0 : 0<L := by linarith [hL.1]
    have hJ0 : 0<J := by linarith [hJ.1]
    have C := hKernel L J hL hJ hSL hSJ
    have e : sourceRhoNormalized X L J=actualNormalizedGram f M δ L J :=
      actual_perturbation_normalized_eq f M hp hδ hL0 hJ0
    dsimp only
    rw [e]
    exact C.2.2

#print axioms certified_actual_family_with_kernel_exists

theorem certified_actual_family_with_kernel_eventually {l : Filter ℕ} {p w P A : ℝ} (hp : 0<p)
    {b d : ℕ→ℕ} {N : ℕ} {R : ℕ→Finset ℕ}
    (h : ∀ᶠ n in l, ActualPacketChoice w (paperV p n (d n)) P A (b n) (d n) N (R n)) :
    ∃ X : ℕ→ℝ→ℝ→ℝ,
       ∀ᶠ n in l, CertifiedActualFamilyWithKernel p w P A n (b n) (d n) N (R n) (X n) := by
  classical
  let W (n : ℕ) (X : ℝ→ℝ→ℝ) := CertifiedActualFamilyWithKernel p w P A n (b n) (d n) N (R n) X
  let X (n : ℕ) := if H : ∃ X, W n X then H.choose else fun _ _ => 0
  refine ⟨X,?_⟩
  filter_upwards [h] with n hn
  have H : ∃ X, W n X := certified_actual_family_with_kernel_exists hp hn
  dsimp only [X]
  rw [dite_eq_left H]
  exact H.choose_spec

#print axioms certified_actual_family_with_kernel_exists
#print axioms certified_actual_family_with_kernel_eventually
end CenteredCubeSqrt
