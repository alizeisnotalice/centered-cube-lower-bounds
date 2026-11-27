import SqrtPlateauTail
import SqrtActualWindowCentered

namespace CenteredCubeSqrt
open Set MeasureTheory
open scoped Interval BigOperators

theorem actualLowSpectrum_variance_eq (M : ℕ) (L : ℝ) :
    periodL2Sq (actualLowSpectrum M L) = (finitePlateau M L-1)/3 := by
  let a (m : ℕ) := lowSpectrumAmp m*Real.sin (((m:ℝ)+1)*Real.pi*L)
  have e (x : ℝ) : actualLowSpectrum M L x =
      ∑ m ∈ Finset.range M, a m*Real.cos (((1+m:ℕ):ℝ)*(2*Real.pi)*x) := by
    unfold actualLowSpectrum
    apply Finset.sum_congr rfl
    intro m _
    simp only [a,Nat.cast_add,Nat.cast_one,add_comm (1:ℝ)]
  unfold periodL2Sq
  simp_rw [e]
  rw [CenteredCube.RudinDensity.integral_cos_series_sq (M:=1) (by decide) a]
  have ea (m : ℕ) : (a m)^2 = (2/3)*plateauSumTerm L (m+1) := by
    unfold a lowSpectrumAmp plateauSumTerm
    rw [mul_pow,Real.sq_sqrt (div_nonneg (mul_nonneg (by norm_num) (plateauSpectralCoeff_nonneg _)) (by norm_num))]
    push_cast
    ring
  simp_rw [ea, ←Finset.mul_sum]
  unfold finitePlateau
  ring

theorem actualLowSpectrum_variance_tail {L : ℝ} (hL : L∈Icc (10/9:ℝ) (11/9))
    {M : ℕ} (hM : 0<M) :
    0≤((27/29)*L^2-1)/3-periodL2Sq (actualLowSpectrum M L) ∧
      ((27/29)*L^2-1)/3-periodL2Sq (actualLowSpectrum M L) ≤ 16/(29*(M:ℝ)^3) := by
  have h := paper_plateau_finite_tail hL hM
  rw [actualLowSpectrum_variance_eq]
  constructor
  · linarith [h.1]
  · have e : (48:ℝ)/(29*(M:ℝ)^3)=3*(16/(29*(M:ℝ)^3)) := by ring
    linarith [h.2]

#print axioms actualLowSpectrum_variance_eq
#print axioms actualLowSpectrum_variance_tail

end CenteredCubeSqrt
