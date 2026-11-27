import SqrtWitnessGramCauchy
import SqrtReferenceKernelGap
import SqrtSpectralMixedGram

namespace CenteredCubeSqrt
open Set MeasureTheory
open scoped BigOperators Interval
set_option maxHeartbeats 750000

theorem sqrt_diagonal_offset {U V : ℝ} (hU : 0≤U) (hV : 0≤V) :
    1/3+Real.sqrt (U*V)≤Real.sqrt ((1/3+U)*(1/3+V)) := by
  apply Real.le_sqrt_of_sq_le
  have e := Real.sqrt_mul hU V
  have Q := sq_nonneg (Real.sqrt U-Real.sqrt V)
  have u := Real.sq_sqrt hU
  have v := Real.sq_sqrt hV
  have w := Real.sq_sqrt (mul_nonneg hU hV)
  rw [e] at w ⊢
  nlinarith

theorem finitePlateau_at_least_one (M : ℕ) (L : ℝ) : 1≤finitePlateau M L := by
  unfold finitePlateau
  linarith [Finset.sum_nonneg (s:=Finset.range M) (fun m _ => plateauSumTerm_nonnegative L (m+1))]

theorem actual_near_reference_cauchy (M : ℕ) (L J : ℝ) {R : ℝ} (hR : |R|≤1/3) :
    |R+periodInner (actualLowSpectrum M L) (actualLowSpectrum M J)|≤
      Real.sqrt ((finitePlateau M L/3)*(finitePlateau M J/3)) := by
  let U := (finitePlateau M L-1)/3
  let V := (finitePlateau M J-1)/3
  have hU : 0≤U := by dsimp [U]; linarith [finitePlateau_at_least_one M L]
  have hV : 0≤V := by dsimp [V]; linarith [finitePlateau_at_least_one M J]
  have h := periodInner_cauchy_both_continuous (actualLowSpectrum_continuous M L)
    (actualLowSpectrum_continuous M J)
  rw [periodInner_self_eq_L2Sq,periodInner_self_eq_L2Sq,
    actualLowSpectrum_variance_eq,actualLowSpectrum_variance_eq] at h
  change |periodInner (actualLowSpectrum M L) (actualLowSpectrum M J)|≤Real.sqrt (U*V) at h
  refine (abs_add_le _ _).trans ((add_le_add hR h).trans ((sqrt_diagonal_offset hU hV).trans_eq ?_))
  congr 1
  simp only [U,V]
  ring

theorem actual_near_reference_one_add_cross (M : ℕ) (L J : ℝ) :
    1+(∑ k ∈ Finset.range M,spectralMixedTerm L J (k+1))≤
      Real.sqrt (finitePlateau M L*finitePlateau M J) := by
  have h := (le_abs_self _).trans (actual_near_reference_cauchy M L J (R:=1/3) (by norm_num))
  rw [actualLowSpectrum_inner_eq] at h
  have hroot : Real.sqrt ((finitePlateau M L/3)*(finitePlateau M J/3)) =
      (1/3)*Real.sqrt (finitePlateau M L*finitePlateau M J) := by
    rw [show finitePlateau M L/3*(finitePlateau M J/3)=(1/9)*(finitePlateau M L*finitePlateau M J) by ring,
      Real.sqrt_mul (by norm_num : (0:ℝ)≤1/9)]
    have hs : Real.sqrt (1/9)=1/3 := by
      rw [show (1:ℝ)/9=(1/3)^2 by norm_num,Real.sqrt_sq (by norm_num)]
    rw [hs]
  rw [hroot] at h
  linarith

#print axioms actual_near_reference_cauchy
#print axioms actual_near_reference_one_add_cross
end CenteredCubeSqrt
