import SqrtActualRawSafeDiagonal
import SqrtBoxGramError
import SqrtAtomicSpectralCross
import SqrtSpectralGramLower
import SqrtKernelDiagonal

namespace CenteredCubeSqrt
open MeasureTheory Set
open scoped Interval BigOperators
set_option maxHeartbeats 1000000
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

noncomputable def actualWitnessGram {B K : ℕ} [NeZero K] (f : ZMod K→Fin B)
    (M : ℕ) (δ L J : ℝ) :=
  periodInner (fun x => actualAtomicWindow f δ L x+actualLowSpectrum M L x)
    (fun x => actualAtomicWindow f δ J x+actualLowSpectrum M J x)

theorem periodInner_self_eq_L2Sq (f : ℝ→ℝ) : periodInner f f=periodL2Sq f := by
  simp only [periodInner,periodL2Sq,pow_two]

theorem actualWitnessGram_diagonal_split {B K : ℕ} [NeZero K] (f : ZMod K→Fin B)
    (M : ℕ) {δ : ℝ} (hδ : 0<δ) (L : ℝ) :
    actualWitnessGram f M δ L L =
      periodInner (actualAtomicWindow f δ L) (actualAtomicWindow f δ L) +
      (periodInner (actualAtomicWindow f δ L) (actualLowSpectrum M L) +
        periodInner (actualLowSpectrum M L) (actualAtomicWindow f δ L)) +
      (finitePlateau M L-1)/3 := by
  have A := actualAtomicWindow_continuous f hδ L
  have S := actualLowSpectrum_continuous M L
  unfold actualWitnessGram
  rw [periodInner_self_eq_L2Sq,periodL2Sq_add A S,actualLowSpectrum_variance_eq,
    periodInner_comm (actualLowSpectrum M L) (actualAtomicWindow f δ L),
    periodInner_self_eq_L2Sq (actualAtomicWindow f δ L)]
  ring

theorem actualWitnessGram_diagonal_error {b d : ℕ} [NeZero (2^d-1)]
    (hd : 0<d) (g : (LabelField d)ˣ) (hg : orderOf g=2^d-1) (t : Fin b → LabelField d)
    (ht : LinearIndependent (ZMod 2) t) (hdim : 2*b≤d) (M : ℕ) (hM : M<2^d-1)
    {δ L : ℝ} (hδ : 0<δ) (hδ1 : δ<1)
    (hδB : δ<1/((((2^b:ℕ):ℝ))*(((2^d-1:ℕ):ℝ))))
    (hKδ : (((2^d-1:ℕ):ℝ))*δ≤1)
    (hK : 18≤(2^d-1:ℕ)) (hL : L∈Icc (10/9:ℝ) (11/9))
    (hSafe : actualSafeLifts hd g hg t L) :
    let K := ((2^d-1:ℕ):ℝ)
    let B := (2:ℝ)^b
    let f := ordinalPhaseLabel hd g hg t
    |actualWitnessGram f M δ L L-finitePlateau M L/3| ≤
      1/(3*B^2)+2/K+ (2/3)*K*δ+manuscriptCrossError B K M := by
  let K := ((2^d-1:ℕ):ℝ)
  let B := (2:ℝ)^b
  let f := ordinalPhaseLabel hd g hg t
  let A := actualAtomicWindow f δ L
  let R := actualRawWindow f L
  let S := actualLowSpectrum M L
  have hL0 : 0≤L := by linarith [hL.1]
  have htn (i : Fin b) : t i≠0 := ht.ne_zero i
  have a := actual_raw_safe_diagonal hd g hg ht hdim hK hL hSafe
  have c := actual_atomic_spectral_cross_bound hd g hg t htn M hM hδ hδ1 hL0 hL0
  have s := actual_atomic_box_gram_error (B:=2^b) (K:=2^d-1) (by positivity) (by omega)
    f hδ hδB hKδ L L
  change |periodInner R R-1/3| ≤ 1/(3*B^2)+2/K at a
  change |periodInner A S+periodInner S A| ≤ manuscriptCrossError B K M at c
  change |periodInner R R-periodInner A A|≤(2/3)*K*δ at s
  have e : actualWitnessGram f M δ L L-finitePlateau M L/3 =
    ((periodInner A A-periodInner R R)+(periodInner R R-1/3))+
      (periodInner A S+periodInner S A) := by
    rw [actualWitnessGram_diagonal_split f M hδ L]
    dsimp only [A,S]
    ring
  change |actualWitnessGram f M δ L L-finitePlateau M L/3| ≤ _
  rw [e]
  refine (abs_add_le _ _).trans ((add_le_add (abs_add_le _ _) le_rfl).trans ?_)
  rw [abs_sub_comm (periodInner A A) (periodInner R R)]
  linarith

#print axioms actualWitnessGram_diagonal_error
end CenteredCubeSqrt
