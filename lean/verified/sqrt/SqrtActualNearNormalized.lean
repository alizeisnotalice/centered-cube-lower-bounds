import SqrtActualNearReference
import SqrtSafeWitnessNearEntry
import SqrtGramNormalization

namespace CenteredCubeSqrt
open Set MeasureTheory
open scoped BigOperators Interval
set_option maxHeartbeats 1200000
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

noncomputable def actualNormalizedGram {B K : ℕ} [NeZero K] (f : ZMod K→Fin B)
    (M : ℕ) (δ L J : ℝ) : ℝ :=
  actualWitnessGram f M δ L J/Real.sqrt (actualWitnessGram f M δ L L*actualWitnessGram f M δ J J)

theorem actual_near_reference_denominator (M : ℕ) {L J : ℝ}
    (hM : 0<M) (hL : L∈Icc (10/9:ℝ) (11/9)) (hJ : J∈Icc (10/9:ℝ) (11/9)) :
    let D := Real.sqrt (finitePlateau M L*finitePlateau M J)
    0<D ∧ D≤121/87 := by
  have l₀ := finitePlateau_at_least_one M L
  have j₀ := finitePlateau_at_least_one M J
  have l₁ := (paper_plateau_finite_tail hL hM).1
  have j₁ := (paper_plateau_finite_tail hJ hM).1
  have ll := (plateau_normalized_bounds hL).2
  have jj := (plateau_normalized_bounds hJ).2
  dsimp only
  constructor
  · positivity
  · apply Real.sqrt_le_iff.mpr
    refine ⟨by norm_num,?_⟩
    rw [sq]
    exact mul_le_mul (by linarith) (by linarith) (by linarith) (by norm_num)

theorem actual_near_gap_normalize_scalar {a b c e τ : ℝ} (M : ℕ) {L J : ℝ}
    (hM : 0<M) (hL : L∈Icc (10/9:ℝ) (11/9)) (hJ : J∈Icc (10/9:ℝ) (11/9))
    (hτ : τ∈Icc (0:ℝ) 1) (ha : 1/4≤a) (hb : 1/4≤b)
    (hA : |a-finitePlateau M L/3|≤e) (hB : |b-finitePlateau M J/3|≤e)
    (hC : |c-((1-τ)^3/3+periodInner (actualLowSpectrum M L) (actualLowSpectrum M J))|≤e)
    (hc : |c|≤Real.sqrt (a*b)) :
    let κ := c/Real.sqrt (a*b)
    (τ≤1/8 → (174/121)*τ-8*e≤1-κ) ∧
    (1/8≤τ → 14703/61952-8*e≤1-κ) := by
  let N := ∑ k ∈ Finset.range M,spectralMixedTerm L J (k+1)
  let D := Real.sqrt (finitePlateau M L*finitePlateau M J)
  let R := (1-τ)^3/3
  let κ₀ := (R+periodInner (actualLowSpectrum M L) (actualLowSpectrum M J))/
    Real.sqrt ((finitePlateau M L/3)*(finitePlateau M J/3))
  have hr₀ : 0≤1-τ := by linarith [hτ.2]
  have hr₁ : 1-τ≤1 := by linarith [hτ.1]
  have hp := pow_le_pow_left₀ hr₀ hr₁ 3
  have hr : |R|≤1/3 := by
    rw [abs_of_nonneg (by dsimp [R]; positivity)]
    dsimp [R]
    linarith
  have hD := actual_near_reference_denominator M hM hL hJ
  have hC' : 1+N≤D := actual_near_reference_one_add_cross M L J
  have href : κ₀=((1-τ)^3+N)/D := by
    unfold κ₀ R
    rw [actualLowSpectrum_inner_eq,
      show finitePlateau M L/3*(finitePlateau M J/3)=(1/9)*(finitePlateau M L*finitePlateau M J) by ring,
      Real.sqrt_mul (by norm_num : (0:ℝ)≤1/9)]
    have hs : Real.sqrt (1/9)=1/3 := by
      rw [show (1:ℝ)/9=(1/3)^2 by norm_num,Real.sqrt_sq (by norm_num)]
    rw [hs]
    change ((1-τ)^3/3+1/3*N)/(1/3*D)=_
    field_simp
  have norm := normalizedEntry_le_eight ha hb
    (by linarith [finitePlateau_at_least_one M L]) (by linarith [finitePlateau_at_least_one M J])
    hA hB hC hc (actual_near_reference_cauchy M L J hr)
  dsimp only
  exact ⟨fun ht => normalized_kernel_small_gap hτ.1 ht hD.1 hD.2 hC' href norm,
    fun ht => normalized_kernel_medium_gap ht hτ.2 hD.1 hD.2 hC' href norm⟩

theorem actualWitnessGram_normalized_near_gaps {b d : ℕ} [NeZero (2^d-1)]
    (hd : 0<d) (g : (LabelField d)ˣ) (hg : orderOf g=2^d-1) (t : Fin b → LabelField d)
    (ht : LinearIndependent (ZMod 2) t) (hdim : 2*b≤d) (M : ℕ) (hM : M<2^d-1) (hM0 : 0<M)
    {δ L J : ℝ} (hδ : 0<δ) (hδ1 : δ<1)
    (hδB : δ<1/((((2^b:ℕ):ℝ))*(((2^d-1:ℕ):ℝ))))
    (hKδ : (((2^d-1:ℕ):ℝ))*δ≤1)
    (hK : 18≤(2^d-1:ℕ)) (hL : L∈Icc (10/9:ℝ) (11/9)) (hJ : J∈Icc (10/9:ℝ) (11/9))
    (hSafeL : actualSafeLifts hd g hg t L) (hSafeJ : actualSafeLifts hd g hg t J)
    (hτ : (((2^d-1:ℕ):ℝ))*(J-L)/2∈Icc (0:ℝ) 1)
    (h1 : (phaseState hd g hg (1:ZMod (2^d-1)) : LabelField d) ≠ 1)
    (h1' : (phaseState hd g hg (1:ZMod (2^d-1)) : LabelField d) ∉ labelRatioSet t)
    (hFloor :
      let K := ((2^d-1:ℕ):ℝ)
      let B := (2:ℝ)^b
      1/4≤100/261-(48/(29*(M:ℝ)^3))/3-
        (1/(3*B^2)+2/K+(2/3)*K*δ+manuscriptCrossError B K M)) :
    let K := ((2^d-1:ℕ):ℝ)
    let B := (2:ℝ)^b
    let f := ordinalPhaseLabel hd g hg t
    let τ := K*(J-L)/2
    let κ := actualNormalizedGram f M δ L J
    let e := 2/(3*B^2)+2/K+(2/3)*K*δ+manuscriptCrossError B K M
    (τ≤1/8 → (174/121)*τ-8*e≤1-κ) ∧
    (1/8≤τ → 14703/61952-8*e≤1-κ) := by
  let K := ((2^d-1:ℕ):ℝ)
  let B := (2:ℝ)^b
  let f := ordinalPhaseLabel hd g hg t
  let A := 1/(3*B^2)+2/K+(2/3)*K*δ+manuscriptCrossError B K M
  let E := 2/(3*B^2)+2/K+(2/3)*K*δ+manuscriptCrossError B K M
  have hb : 0≤1/(3*B^2) := by positivity
  have hAE : A≤E := by
    dsimp only [A,E]
    have F : 2/(3*B^2)=2*(1/(3*B^2)) := by ring
    linarith
  have F (x : ℝ) (hx : x∈Icc (10/9:ℝ) (11/9)) (hs : actualSafeLifts hd g hg t x) :
      1/4≤actualWitnessGram f M δ x x ∧
      |actualWitnessGram f M δ x x-finitePlateau M x/3|≤E := by
    have hD : |actualWitnessGram f M δ x x-finitePlateau M x/3|≤A :=
      actualWitnessGram_diagonal_error hd g hg t ht hdim M hM hδ hδ1 hδB hKδ hK hx hs
    have hG := (paper_kernel_diagonal_assembly hx (paper_plateau_finite_tail hx hM0) hD).1
    exact ⟨hFloor.trans hG,hD.trans hAE⟩
  have hA := F L hL hSafeL
  have hB := F J hJ hSafeJ
  have hC := actualWitnessGram_near_entry_error hd g hg t ht hdim M hM hδ hδ1 hδB hKδ hK hL hJ hSafeL hτ h1 h1'
  have hc := witnessGram_entry_cauchy f M hδ L J
  exact actual_near_gap_normalize_scalar M hM0 hL hJ hτ hA.1 hB.1 hA.2 hB.2 hC hc

#print axioms actual_near_gap_normalize_scalar
#print axioms actualWitnessGram_normalized_near_gaps
end CenteredCubeSqrt
