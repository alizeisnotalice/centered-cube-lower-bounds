import SqrtKernelEventually

namespace CenteredCubeSqrt
open Set MeasureTheory
open scoped BigOperators Interval
set_option maxHeartbeats 1300000
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem actualNormalizedGram_comm {B K : ℕ} [NeZero K] (f : ZMod K→Fin B)
    (M : ℕ) (δ L J : ℝ) :
    actualNormalizedGram f M δ L J=actualNormalizedGram f M δ J L := by
  unfold actualNormalizedGram actualWitnessGram periodInner
  simp only [mul_comm]

theorem actualWitnessGram_uniform_safe_kernel {b d : ℕ} [NeZero (2^d-1)]
    (hd : 0<d) (g : (LabelField d)ˣ) (hg : orderOf g=2^d-1) (t : Fin b → LabelField d)
    (ht : LinearIndependent (ZMod 2) t) (hdim : 2*b≤d) (M : ℕ) (hM : M<2^d-1) (hM0 : 0<M)
    {δ L J Q : ℝ} (hδ : 0<δ) (hδ1 : δ<1)
    (hδB : δ<1/((((2^b:ℕ):ℝ))*(((2^d-1:ℕ):ℝ))))
    (hKδ : (((2^d-1:ℕ):ℝ))*δ≤1)
    (hK : 18≤(2^d-1:ℕ)) (hL : L∈Icc (10/9:ℝ) (11/9)) (hJ : J∈Icc (10/9:ℝ) (11/9))
    (hSafeL : actualSafeLifts hd g hg t L) (hSafeJ : actualSafeLifts hd g hg t J)
    (h1 : (phaseState hd g hg (1:ZMod (2^d-1)) : LabelField d) ≠ 1)
    (h1' : (phaseState hd g hg (1:ZMod (2^d-1)) : LabelField d) ∉ labelRatioSet t)
    (hC : ∀ z : ℝ, ((⌊z⌋:ℤ):ZMod (2^d-1)) ≠0 → (((⌊z⌋:ℤ)+1:ℤ):ZMod (2^d-1)) ≠0 →
      |rawCorrelation (ordinalPhaseLabel hd g hg t) z|≤Q)
    (hQ : Q≤21/500)
    (hE :
      let K := ((2^d-1:ℕ):ℝ)
      let B := (2:ℝ)^b
      (2/3)*K*δ+manuscriptCrossError B K M≤1/1000)
    (hEN :
      let K := ((2^d-1:ℕ):ℝ)
      let B := (2:ℝ)^b
      2/(3*B^2)+2/K+(2/3)*K*δ+manuscriptCrossError B K M≤1/1000)
    (hV :
      let K := ((2^d-1:ℕ):ℝ)
      let B := (2:ℝ)^b
      19/50≤100/261-(48/(29*(M:ℝ)^3))/3-
        (1/(3*B^2)+2/K+(2/3)*K*δ+manuscriptCrossError B K M)) :
    let K := ((2^d-1:ℕ):ℝ)
    let f := ordinalPhaseLabel hd g hg t
    let τ := K * |J-L|/2
    let κ := actualNormalizedGram f M δ L J
    ((-(1/2:ℝ)≤κ) ∧ (1/8≤τ → 1/5≤1-κ)) := by
  let K := ((2^d-1:ℕ):ℝ)
  let B := (2:ℝ)^b
  let E := (2/3)*K*δ+manuscriptCrossError B K M
  let EN := 2/(3*B^2)+2/K+(2/3)*K*δ+manuscriptCrossError B K M
  let V := 100/261-(48/(29*(M:ℝ)^3))/3-(1/(3*B^2)+2/K+(2/3)*K*δ+manuscriptCrossError B K M)
  let f := ordinalPhaseLabel hd g hg t
  have hV' : 19/50≤V := hV
  have hp : 0<V := by linarith
  have hquarter : 1/4≤V := by linarith
  have X (P R : ℝ) (hP : P∈Icc (10/9:ℝ) (11/9)) (hR : R∈Icc (10/9:ℝ) (11/9))
      (hSP : actualSafeLifts hd g hg t P) (hSR : actualSafeLifts hd g hg t R) (hPR : P≤R) :
      let κ := actualNormalizedGram f M δ P R
      ((-(1/2:ℝ)≤κ) ∧ (1/8≤K * |R-P|/2 → 1/5≤1-κ)) := by
    let τ := K*(R-P)/2
    let κ := actualNormalizedGram f M δ P R
    have ho : 0≤R-P := sub_nonneg.mpr hPR
    have hτ : 0≤τ := by dsimp [τ,K]; positivity
    dsimp only
    rw [abs_of_nonneg ho]
    change -(1/2:ℝ)≤κ ∧ (1/8≤τ → 1/5≤1-κ)
    by_cases h : τ≤1
    · have hIn : τ∈Icc (0:ℝ) 1 := ⟨hτ,h⟩
      have hi := (actualWitnessGram_normalized_near_gaps hd g hg t ht hdim M hM hM0 hδ hδ1
          hδB hKδ hK hP hR hSP hSR hIn h1 h1' hquarter).2
      have lo := actualWitnessGram_normalized_near_lower hd g hg t ht hdim M hM hM0 hδ hδ1
        hδB hKδ hK hP hR hSP hSR hIn h1 h1' hquarter
      exact normalized_kernel_uniform_near_margin hEN lo hi
    · have ht' : 1≤τ := le_of_lt (lt_of_not_ge h)
      have F := actualWitnessGram_normalized_far_assembly hd g hg t ht hdim M hM hM0 hδ hδ1
        hδB hKδ hK hP hR hSP hSR ht' hC hp
      have X : 100/261-(48/(29*(M:ℝ)^3))/3-(1/(3*B^2)+2/K+E)=V := by
        dsimp only [V,E]
        ring
      change (-(4*Q+1/116+E)/(100/261-(48/(29*(M:ℝ)^3))/3-(1/(3*B^2)+2/K+E)) ≤ κ) ∧
        (κ ≤ (4*Q+34/261+E)/(100/261-(48/(29*(M:ℝ)^3))/3-(1/(3*B^2)+2/K+E))) at F
      rw [X] at F
      have h := normalized_kernel_uniform_far_margin hQ hE hV' F
      exact ⟨h.1,fun _ => h.2⟩
  rcases le_total L J with h|h
  · exact X L J hL hJ hSafeL hSafeJ h
  · have H := X J L hJ hL hSafeJ hSafeL h
    dsimp only at H ⊢
    rw [abs_sub_comm L J,actualNormalizedGram_comm f M δ J L] at H
    exact H

#print axioms actualWitnessGram_uniform_safe_kernel
end CenteredCubeSqrt
