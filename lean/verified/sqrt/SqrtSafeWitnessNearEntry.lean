import SqrtRawNearReflection
import SqrtSafeWitnessGramDiagonal

namespace CenteredCubeSqrt
open MeasureTheory Set
open scoped Interval BigOperators
set_option maxHeartbeats 1000000
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem raw_near_covariance_from_corr {B K : ℕ} [NeZero K] (f : ZMod K→Fin B)
    (L J X : ℝ) (hC : |rawCorrelation f ((K:ℝ)*(J-L)/2)-(1-(K:ℝ)*(J-L)/2)^3/6|≤
      1/(4*X^2)+1/(2*(K:ℝ))) (hR : |rawCorrelation f ((K:ℝ)*((L+J)/2))|≤
      1/(12*X^2)+1/(2*(K:ℝ))) :
    |periodInner (actualRawWindow f L) (actualRawWindow f J)-(1-(K:ℝ)*(J-L)/2)^3/3|≤
      2/(3*X^2)+2/(K:ℝ) := by
  let C := rawCorrelation f ((K:ℝ)*(J-L)/2)
  let R := rawCorrelation f ((K:ℝ)*((L+J)/2))
  let F := (1-(K:ℝ)*(J-L)/2)^3/6
  rw [rawWindow_covariance_from_correlation f L J,show (K:ℝ)*(J+L)/2=(K:ℝ)*((L+J)/2) by ring]
  change |2*C-2*R-(1-(K:ℝ)*(J-L)/2)^3/3|≤_
  rw [show 2*C-2*R-(1-(K:ℝ)*(J-L)/2)^3/3=2*(C-F)+(-(2*R)) by unfold F; ring]
  refine (abs_add_le _ _).trans ?_
  rw [abs_neg,abs_mul,abs_mul,abs_of_nonneg (by norm_num : 0≤(2:ℝ))]
  change 2*|C-F|+2*|R|≤_
  change |C-F|≤1/(4*X^2)+1/(2*(K:ℝ)) at hC
  change |R|≤1/(12*X^2)+1/(2*(K:ℝ)) at hR
  calc
    _ ≤ 2*(1/(4*X^2)+1/(2*(K:ℝ))) + 2*(1/(12*X^2)+1/(2*(K:ℝ))) := by linarith
    _ = _ := by ring

theorem actual_raw_near_window_covariance {b d : ℕ} [NeZero (2^d-1)]
    (hd : 0<d) (g : (LabelField d)ˣ) (hg : orderOf g=2^d-1) {t : Fin b → LabelField d}
    (ht : LinearIndependent (ZMod 2) t) (hdim : 2*b≤d)
    {L J : ℝ} (hK : 18≤(2^d-1:ℕ)) (hL : L∈Icc (10/9:ℝ) (11/9)) (hJ : J∈Icc (10/9:ℝ) (11/9))
    (hSafe : actualSafeLifts hd g hg t L)
    (hτ : (((2^d-1:ℕ):ℝ))*(J-L)/2∈Icc (0:ℝ) 1)
    (h1 : (phaseState hd g hg (1:ZMod (2^d-1)) : LabelField d) ≠ 1)
    (h1' : (phaseState hd g hg (1:ZMod (2^d-1)) : LabelField d) ∉ labelRatioSet t) :
    let f := ordinalPhaseLabel hd g hg t
    let K := ((2^d-1:ℕ):ℝ)
    let τ := K*(J-L)/2
    |periodInner (actualRawWindow f L) (actualRawWindow f J)-(1-τ)^3/3|≤
      2/(3*((2:ℝ)^b)^2)+2/K := by
  exact raw_near_covariance_from_corr (ordinalPhaseLabel hd g hg t) L J ((2:ℝ)^b)
    (actual_raw_near_correlation_bound hd g hg ht hdim hτ h1 h1')
    (actual_raw_near_reflected_correlation_bound hd g hg ht hdim hK hL hJ hSafe hτ)

theorem periodInner_add_left {F G H : ℝ→ℝ} (hF : Continuous F) (hG : Continuous G) (hH : Continuous H) :
    periodInner (fun x => F x+G x) H=periodInner F H+periodInner G H := by
  unfold periodInner
  simp_rw [add_mul]
  exact intervalIntegral.integral_add ((hF.mul hH).intervalIntegrable _ _)
    ((hG.mul hH).intervalIntegrable _ _)

theorem actualWitnessGram_entry_split {B K : ℕ} [NeZero K] (f : ZMod K→Fin B)
    (M : ℕ) {δ : ℝ} (hδ : 0<δ) (L J : ℝ) :
    actualWitnessGram f M δ L J =
      periodInner (actualAtomicWindow f δ L) (actualAtomicWindow f δ J) +
      (periodInner (actualAtomicWindow f δ L) (actualLowSpectrum M J) +
        periodInner (actualLowSpectrum M L) (actualAtomicWindow f δ J)) +
      periodInner (actualLowSpectrum M L) (actualLowSpectrum M J) := by
  have hA (x : ℝ) := actualAtomicWindow_continuous f hδ x
  have hB (x : ℝ) := actualLowSpectrum_continuous M x
  unfold actualWitnessGram
  have hF : Continuous (fun x => actualAtomicWindow f δ L x+actualLowSpectrum M L x) :=
    (hA L).add (hB L)
  rw [periodInner_add_right hF (hA J) (hB J),
    periodInner_add_left (hA L) (hB L) (hA J),periodInner_add_left (hA L) (hB L) (hB J)]
  ring

theorem actualWitnessGram_near_entry_error {b d : ℕ} [NeZero (2^d-1)]
    (hd : 0<d) (g : (LabelField d)ˣ) (hg : orderOf g=2^d-1) (t : Fin b → LabelField d)
    (ht : LinearIndependent (ZMod 2) t) (hdim : 2*b≤d) (M : ℕ) (hM : M<2^d-1)
    {δ L J : ℝ} (hδ : 0<δ) (hδ1 : δ<1)
    (hδB : δ<1/((((2^b:ℕ):ℝ))*(((2^d-1:ℕ):ℝ))))
    (hKδ : (((2^d-1:ℕ):ℝ))*δ≤1)
    (hK : 18≤(2^d-1:ℕ)) (hL : L∈Icc (10/9:ℝ) (11/9)) (hJ : J∈Icc (10/9:ℝ) (11/9))
    (hSafe : actualSafeLifts hd g hg t L)
    (hτ : (((2^d-1:ℕ):ℝ))*(J-L)/2∈Icc (0:ℝ) 1)
    (h1 : (phaseState hd g hg (1:ZMod (2^d-1)) : LabelField d) ≠ 1)
    (h1' : (phaseState hd g hg (1:ZMod (2^d-1)) : LabelField d) ∉ labelRatioSet t) :
    let K := ((2^d-1:ℕ):ℝ)
    let B := (2:ℝ)^b
    let f := ordinalPhaseLabel hd g hg t
    let τ := K*(J-L)/2
    |actualWitnessGram f M δ L J-
      ((1-τ)^3/3+periodInner (actualLowSpectrum M L) (actualLowSpectrum M J))|≤
      2/(3*B^2)+2/K+ (2/3)*K*δ+manuscriptCrossError B K M := by
  let K := ((2^d-1:ℕ):ℝ)
  let B := (2:ℝ)^b
  let f := ordinalPhaseLabel hd g hg t
  let A (x : ℝ) := actualAtomicWindow f δ x
  let R (x : ℝ) := actualRawWindow f x
  let S := actualLowSpectrum M
  let τ := K*(J-L)/2
  have hL0 : 0≤L := by linarith [hL.1]
  have hJ0 : 0≤J := by linarith [hJ.1]
  have htn (i : Fin b) : t i≠0 := ht.ne_zero i
  have a := actual_raw_near_window_covariance hd g hg ht hdim hK hL hJ hSafe hτ h1 h1'
  have c := actual_atomic_spectral_cross_bound hd g hg t htn M hM hδ hδ1 hL0 hJ0
  have s := actual_atomic_box_gram_error (B:=2^b) (K:=2^d-1) (by positivity) (by omega)
    f hδ hδB hKδ L J
  change |periodInner (R L) (R J)-(1-τ)^3/3|≤2/(3*B^2)+2/K at a
  change |periodInner (A L) (S J)+periodInner (S L) (A J)|≤manuscriptCrossError B K M at c
  change |periodInner (R L) (R J)-periodInner (A L) (A J)|≤(2/3)*K*δ at s
  have e : actualWitnessGram f M δ L J-((1-τ)^3/3+periodInner (S L) (S J)) =
    ((periodInner (A L) (A J)-periodInner (R L) (R J))+(periodInner (R L) (R J)-(1-τ)^3/3))+
      (periodInner (A L) (S J)+periodInner (S L) (A J)) := by
    rw [actualWitnessGram_entry_split f M hδ L J]
    dsimp only [A,S]
    ring
  change |actualWitnessGram f M δ L J-((1-τ)^3/3+periodInner (S L) (S J))|≤_
  rw [e]
  refine (abs_add_le _ _).trans ((add_le_add (abs_add_le _ _) le_rfl).trans ?_)
  rw [abs_sub_comm (periodInner (A L) (A J)) (periodInner (R L) (R J))]
  linarith

#print axioms actual_raw_near_window_covariance
#print axioms actualWitnessGram_near_entry_error
end CenteredCubeSqrt
