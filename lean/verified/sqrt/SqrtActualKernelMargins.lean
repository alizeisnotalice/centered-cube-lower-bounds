import SqrtActualNearNormalized
import SqrtSpectralGramLower

namespace CenteredCubeSqrt
open Set MeasureTheory
open scoped BigOperators Interval
set_option maxHeartbeats 750000

theorem actualLowSpectrum_cross_upper (M : ℕ) {L J : ℝ} (hM : 0<M)
    (hL : L∈Icc (10/9:ℝ) (11/9)) (hJ : J∈Icc (10/9:ℝ) (11/9)) :
    periodInner (actualLowSpectrum M L) (actualLowSpectrum M J)≤34/261 := by
  have h := periodInner_cauchy_both_continuous (actualLowSpectrum_continuous M L)
    (actualLowSpectrum_continuous M J)
  rw [periodInner_self_eq_L2Sq,periodInner_self_eq_L2Sq,actualLowSpectrum_variance_eq,
    actualLowSpectrum_variance_eq] at h
  have l₀ := finitePlateau_at_least_one M L
  have j₀ := finitePlateau_at_least_one M J
  have l₁ := (paper_plateau_finite_tail hL hM).1
  have j₁ := (paper_plateau_finite_tail hJ hM).1
  have ll := (plateau_normalized_bounds hL).2
  have jj := (plateau_normalized_bounds hJ).2
  refine (le_abs_self _).trans (h.trans (Real.sqrt_le_iff.mpr ⟨by norm_num,?_⟩))
  rw [sq]
  exact mul_le_mul (by linarith) (by linarith) (by linarith) (by norm_num)

theorem actual_normalized_reference_near_lower (M : ℕ) {L J R : ℝ} (hM : 0<M)
    (hL : L∈Icc (10/9:ℝ) (11/9)) (hJ : J∈Icc (10/9:ℝ) (11/9)) (hR : 0≤R) :
    -(34/121:ℝ) ≤ (R+periodInner (actualLowSpectrum M L) (actualLowSpectrum M J))/
      Real.sqrt ((finitePlateau M L/3)*(finitePlateau M J/3)) := by
  let U := finitePlateau M L
  let V := finitePlateau M J
  let D := Real.sqrt ((U/3)*(V/3))
  have hU : 1≤U := finitePlateau_at_least_one M L
  have hV : 1≤V := finitePlateau_at_least_one M J
  have hU' : U≤121/87 := by dsimp [U]; linarith [(paper_plateau_finite_tail hL hM).1,(plateau_normalized_bounds hL).2]
  have hV' : V≤121/87 := by dsimp [V]; linarith [(paper_plateau_finite_tail hJ hM).1,(plateau_normalized_bounds hJ).2]
  have a : (U-1)/3≤(34/121)*(U/3) := by linarith
  have b : (V-1)/3≤(34/121)*(V/3) := by linarith
  have hd : 0<D := by unfold D; positivity
  have h := periodInner_cauchy_both_continuous (actualLowSpectrum_continuous M L)
    (actualLowSpectrum_continuous M J)
  rw [periodInner_self_eq_L2Sq,periodInner_self_eq_L2Sq,actualLowSpectrum_variance_eq,
    actualLowSpectrum_variance_eq] at h
  have H : Real.sqrt ((U-1)/3*((V-1)/3))≤(34/121)*D := by
    calc
      _ ≤ Real.sqrt (((34/121)*(U/3))*((34/121)*(V/3))) :=
        Real.sqrt_le_sqrt (mul_le_mul a b (by linarith) (by positivity))
      _ = _ := by
        rw [show (34/121)*(U/3)*((34/121)*(V/3))=(34/121)^2*((U/3)*(V/3)) by ring,
          Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
  change |periodInner (actualLowSpectrum M L) (actualLowSpectrum M J)|≤_ at h
  change -(34/121:ℝ)≤(_+_)/D
  apply (le_div_iff₀ hd).2
  linarith [(abs_le.mp (h.trans H)).1]

theorem kernel_far_ratio_bounds {a b c V X E : ℝ} (hV : 0<V) (ha : V≤a) (hb : V≤b)
    (hlo : -(X+1/116+E)≤c) (hhi : c≤X+34/261+E)
    (hXE : 0≤X+E) :
    -(X+1/116+E)/V≤c/Real.sqrt (a*b) ∧
      c/Real.sqrt (a*b)≤(X+34/261+E)/V := by
  have h : V≤Real.sqrt (a*b) := Real.le_sqrt_of_sq_le
    (by rw [sq]; exact mul_le_mul ha hb hV.le (hV.le.trans ha))
  have hd : 0<Real.sqrt (a*b) := hV.trans_le h
  constructor
  · calc
      _ ≤ -(X+1/116+E)/Real.sqrt (a*b) := by
        rw [neg_div,neg_div,neg_le_neg_iff]
        exact div_le_div_of_nonneg_left (by linarith) hV h
      _ ≤ _ := div_le_div_of_nonneg_right hlo hd.le
  · exact (div_le_div_of_nonneg_right hhi hd.le).trans
      (div_le_div_of_nonneg_left (by linarith) hV h)

theorem actual_near_gap_lower_scalar {a b c e τ : ℝ} (M : ℕ) {L J : ℝ}
    (hM : 0<M) (hL : L∈Icc (10/9:ℝ) (11/9)) (hJ : J∈Icc (10/9:ℝ) (11/9))
    (hτ : τ∈Icc (0:ℝ) 1) (ha : 1/4≤a) (hb : 1/4≤b)
    (hA : |a-finitePlateau M L/3|≤e) (hB : |b-finitePlateau M J/3|≤e)
    (hC : |c-((1-τ)^3/3+periodInner (actualLowSpectrum M L) (actualLowSpectrum M J))|≤e)
    (hc : |c|≤Real.sqrt (a*b)) :
    -(34/121:ℝ)-8*e≤c/Real.sqrt (a*b) := by
  have hp : 0≤1-τ := by linarith [hτ.2]
  have hP := pow_le_pow_left₀ hp (by linarith [hτ.1] : 1-τ≤1) 3
  have hR : |(1-τ)^3/3|≤1/3 := by rw [abs_of_nonneg (by positivity)]; linarith
  have hN := normalizedEntry_le_eight ha hb
    (by linarith [finitePlateau_at_least_one M L]) (by linarith [finitePlateau_at_least_one M J])
    hA hB hC hc (actual_near_reference_cauchy M L J hR)
  have hK := actual_normalized_reference_near_lower M hM hL hJ
    (show 0≤(1-τ)^3/3 by positivity)
  linarith [(abs_le.mp hN).1]

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem actualWitnessGram_normalized_near_lower {b d : ℕ} [NeZero (2^d-1)]
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
    let κ := actualNormalizedGram f M δ L J
    let e := 2/(3*B^2)+2/K+(2/3)*K*δ+manuscriptCrossError B K M
    (-(34/121:ℝ)-8*e≤κ) := by
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
  exact actual_near_gap_lower_scalar M hM0 hL hJ hτ hA.1 hB.1 hA.2 hB.2 hC hc

#print axioms actualWitnessGram_normalized_near_lower
#print axioms actual_near_gap_lower_scalar
#print axioms actualLowSpectrum_cross_upper
#print axioms actual_normalized_reference_near_lower
#print axioms kernel_far_ratio_bounds
end CenteredCubeSqrt
