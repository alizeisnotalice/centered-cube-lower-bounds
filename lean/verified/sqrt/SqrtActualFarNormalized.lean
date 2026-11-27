import SqrtActualFarCarries
import SqrtActualKernelMargins

namespace CenteredCubeSqrt
open Set MeasureTheory
open scoped BigOperators Interval
set_option maxHeartbeats 1150000
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem actualWitnessGram_smoothing_cross_error {b d : ℕ} [NeZero (2^d-1)]
    (hd : 0<d) (g : (LabelField d)ˣ) (hg : orderOf g=2^d-1) (t : Fin b → LabelField d)
    (ht : LinearIndependent (ZMod 2) t) (M : ℕ) (hM : M<2^d-1)
    {δ L J : ℝ} (hδ : 0<δ) (hδ1 : δ<1)
    (hδB : δ<1/((((2^b:ℕ):ℝ))*(((2^d-1:ℕ):ℝ))))
    (hKδ : (((2^d-1:ℕ):ℝ))*δ≤1) (hK : 2≤(2^d-1:ℕ)) (hL : 0≤L) (hJ : 0≤J) :
    let K := ((2^d-1:ℕ):ℝ)
    let B := (2:ℝ)^b
    let f := ordinalPhaseLabel hd g hg t
    |actualWitnessGram f M δ L J -
      (periodInner (actualRawWindow f L) (actualRawWindow f J)+
        periodInner (actualLowSpectrum M L) (actualLowSpectrum M J))|≤
      (2/3)*K*δ + manuscriptCrossError B K M := by
  let K := ((2^d-1:ℕ):ℝ)
  let B := (2:ℝ)^b
  let f := ordinalPhaseLabel hd g hg t
  let A (x : ℝ) := actualAtomicWindow f δ x
  let R (x : ℝ) := actualRawWindow f x
  let S := actualLowSpectrum M
  have htn (i : Fin b) : t i≠0 := ht.ne_zero i
  have c := actual_atomic_spectral_cross_bound hd g hg t htn M hM hδ hδ1 hL hJ
  have s := actual_atomic_box_gram_error (B:=2^b) (K:=2^d-1) (by positivity) hK f hδ hδB hKδ L J
  change |periodInner (A L) (S J)+periodInner (S L) (A J)|≤manuscriptCrossError B K M at c
  change |periodInner (R L) (R J)-periodInner (A L) (A J)|≤(2/3)*K*δ at s
  have e : actualWitnessGram f M δ L J-(periodInner (R L) (R J)+periodInner (S L) (S J)) =
    (periodInner (A L) (A J)-periodInner (R L) (R J))+
      (periodInner (A L) (S J)+periodInner (S L) (A J)) := by
    rw [actualWitnessGram_entry_split f M hδ L J]
    dsimp only [A,S]
    ring
  change |actualWitnessGram f M δ L J-(periodInner (R L) (R J)+periodInner (S L) (S J))|≤_
  rw [e]
  refine (abs_add_le _ _).trans ?_
  rw [abs_sub_comm (periodInner (A L) (A J)) (periodInner (R L) (R J))]
  exact add_le_add s c

theorem actualWitnessGram_normalized_far_assembly {b d : ℕ} [NeZero (2^d-1)]
    (hd : 0<d) (g : (LabelField d)ˣ) (hg : orderOf g=2^d-1) (t : Fin b → LabelField d)
    (ht : LinearIndependent (ZMod 2) t) (hdim : 2*b≤d) (M : ℕ) (hM : M<2^d-1) (hM0 : 0<M)
    {δ L J Q : ℝ} (hδ : 0<δ) (hδ1 : δ<1)
    (hδB : δ<1/((((2^b:ℕ):ℝ))*(((2^d-1:ℕ):ℝ))))
    (hKδ : (((2^d-1:ℕ):ℝ))*δ≤1)
    (hK : 18≤(2^d-1:ℕ)) (hL : L∈Icc (10/9:ℝ) (11/9)) (hJ : J∈Icc (10/9:ℝ) (11/9))
    (hSafeL : actualSafeLifts hd g hg t L) (hSafeJ : actualSafeLifts hd g hg t J)
    (hτ : 1≤(((2^d-1:ℕ):ℝ))*(J-L)/2)
    (hC : ∀ z : ℝ, ((⌊z⌋:ℤ):ZMod (2^d-1)) ≠0 → (((⌊z⌋:ℤ)+1:ℤ):ZMod (2^d-1)) ≠0 →
      |rawCorrelation (ordinalPhaseLabel hd g hg t) z|≤Q)
    (hFloor :
      let K := ((2^d-1:ℕ):ℝ)
      let B := (2:ℝ)^b
      0<100/261-(48/(29*(M:ℝ)^3))/3-
        (1/(3*B^2)+2/K+(2/3)*K*δ+manuscriptCrossError B K M)) :
    let K := ((2^d-1:ℕ):ℝ)
    let B := (2:ℝ)^b
    let f := ordinalPhaseLabel hd g hg t
    let E := (2/3)*K*δ+manuscriptCrossError B K M
    let V := 100/261-(48/(29*(M:ℝ)^3))/3-(1/(3*B^2)+2/K+E)
    let κ := actualNormalizedGram f M δ L J
    ((-(4*Q+1/116+E)/V ≤ κ) ∧ (κ ≤ (4*Q+34/261+E)/V)) := by
  let K := ((2^d-1:ℕ):ℝ)
  let B := (2:ℝ)^b
  let f := ordinalPhaseLabel hd g hg t
  let E := (2/3)*K*δ+manuscriptCrossError B K M
  let V := 100/261-(48/(29*(M:ℝ)^3))/3-(1/(3*B^2)+2/K+E)
  let A := periodInner (actualRawWindow f L) (actualRawWindow f J)
  let S := periodInner (actualLowSpectrum M L) (actualLowSpectrum M J)
  let C := actualWitnessGram f M δ L J
  have G (x : ℝ) (hx : x∈Icc (10/9:ℝ) (11/9)) (hs : actualSafeLifts hd g hg t x) :
      V≤actualWitnessGram f M δ x x := by
    have hD := actualWitnessGram_diagonal_error hd g hg t ht hdim M hM hδ hδ1 hδB hKδ hK hx hs
    have hD' : |actualWitnessGram f M δ x x-finitePlateau M x/3|≤1/(3*B^2)+2/K+E := by
      convert hD using 1
      dsimp [E]
      ring
    exact (paper_kernel_diagonal_assembly hx (paper_plateau_finite_tail hx hM0) hD').1
  have hF : 0<V := by
    dsimp [V,E]
    dsimp only at hFloor
    linarith
  have hA : |A|≤4*Q := actualRaw_far_covariance_from_nonzero f hK hL hJ hτ hC
  have hLo : -(1/116:ℝ)≤S := actualLowSpectrum_cross_lower hL hJ M
  have hHi : S≤34/261 := actualLowSpectrum_cross_upper M hM0 hL hJ
  have hE : |C-(A+S)|≤E :=
    actualWitnessGram_smoothing_cross_error hd g hg t ht M hM hδ hδ1 hδB hKδ (by omega)
      (by linarith [hL.1]) (by linarith [hJ.1])
  have lo : -(4*Q+1/116+E)≤C := by linarith [(abs_le.mp hA).1,(abs_le.mp hE).1]
  have hi : C≤4*Q+34/261+E := by linarith [(abs_le.mp hA).2,(abs_le.mp hE).2]
  change -(4*Q+1/116+E)/V≤actualNormalizedGram f M δ L J ∧
    actualNormalizedGram f M δ L J≤(4*Q+34/261+E)/V
  exact kernel_far_ratio_bounds hF (G L hL hSafeL) (G J hJ hSafeJ) lo hi
    (add_nonneg ((abs_nonneg _).trans hA) ((abs_nonneg _).trans hE))

#print axioms actualWitnessGram_smoothing_cross_error
#print axioms actualWitnessGram_normalized_far_assembly
end CenteredCubeSqrt
