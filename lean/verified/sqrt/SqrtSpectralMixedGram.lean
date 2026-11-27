import SqrtPlateauLowVariance

namespace CenteredCubeSqrt
open MeasureTheory Set
open scoped Interval BigOperators
set_option maxHeartbeats 1200000

noncomputable def spectralMixedTerm (L J : ℝ) (m : ℕ) : ℝ :=
  plateauSpectralCoeff m*Real.sin (Real.pi*(m:ℝ)*L)*Real.sin (Real.pi*(m:ℝ)*J)

theorem actualLowSpectrum_inner_eq (M : ℕ) (L J : ℝ) :
    periodInner (actualLowSpectrum M L) (actualLowSpectrum M J) =
      (1/3)*∑ k ∈ Finset.range M,spectralMixedTerm L J (k+1) := by
  let a (m : ℕ) (x : ℝ) := lowSpectrumAmp m*Real.sin (((m:ℝ)+1)*Real.pi*x)
  have e (x : ℝ) (y : ℝ) : actualLowSpectrum M x y =
      ∑ m ∈ Finset.range M, a m x*Real.cos (((1+m:ℕ):ℝ)*(2*Real.pi)*y) := by
    unfold actualLowSpectrum
    apply Finset.sum_congr rfl
    intro m _
    simp only [a,Nat.cast_add,Nat.cast_one,add_comm (1:ℝ)]
  unfold periodInner
  simp_rw [e]
  rw [CenteredCube.RudinDensity.integral_cos_series_mul (M:=1) (by decide) (fun m => a m L) (fun m => a m J)]
  have ea (m : ℕ) : a m L*a m J = (2/3)*spectralMixedTerm L J (m+1) := by
    unfold a spectralMixedTerm
    rw [show lowSpectrumAmp m*Real.sin (((m:ℝ)+1)*Real.pi*L)*
      (lowSpectrumAmp m*Real.sin (((m:ℝ)+1)*Real.pi*J)) =
        lowSpectrumAmp m^2*Real.sin (((m:ℝ)+1)*Real.pi*L)*Real.sin (((m:ℝ)+1)*Real.pi*J) by ring]
    unfold lowSpectrumAmp
    rw [Real.sq_sqrt (div_nonneg (mul_nonneg (by norm_num) (plateauSpectralCoeff_nonneg _)) (by norm_num))]
    push_cast
    rw [show ((m:ℝ)+1)*Real.pi=Real.pi*((m:ℝ)+1) by ring]
    ring
  simp_rw [ea,←Finset.mul_sum]
  ring

theorem shifted_harmonic_product_nonneg {L J : ℝ} (hL : L∈Icc (10/9:ℝ) (11/9))
    (hJ : J∈Icc (10/9:ℝ) (11/9)) {m : ℕ} (hm : m≤4) :
    0≤spectralMixedTerm L J m := by
  have e (x : ℝ) : Real.sin (Real.pi*(m:ℝ)*x) =
      (-1:ℝ)^m*Real.sin (Real.pi*(m:ℝ)*(x-1)) := by
    rw [show Real.pi*(m:ℝ)*x=Real.pi*(m:ℝ)*(x-1)+(m:ℝ)*Real.pi by ring]
    exact Real.sin_add_nat_mul_pi _ _
  have H (x : ℝ) (hx : x∈Icc (10/9:ℝ) (11/9)) :
      0≤Real.sin (Real.pi*(m:ℝ)*(x-1)) := by
    have hx0 : 0≤x-1 := by linarith [hx.1]
    have hm0 : 0≤(m:ℝ) := by positivity
    have hm1 : (m:ℝ)≤4 := by exact_mod_cast hm
    have h := mul_le_mul hm1 (show x-1≤2/9 by linarith [hx.2]) hx0 (by norm_num : 0≤(4:ℝ))
    apply Real.sin_nonneg_of_nonneg_of_le_pi (by positivity)
    have hh := mul_le_mul_of_nonneg_left h Real.pi_pos.le
    nlinarith [Real.pi_pos]
  unfold spectralMixedTerm
  rw [e L,e J]
  have E : plateauSpectralCoeff m*((-1:ℝ)^m*Real.sin (Real.pi*(m:ℝ)*(L-1)))*
      ((-1:ℝ)^m*Real.sin (Real.pi*(m:ℝ)*(J-1))) =
    (((-1:ℝ)^m)^2)*(plateauSpectralCoeff m*Real.sin (Real.pi*(m:ℝ)*(L-1))*
      Real.sin (Real.pi*(m:ℝ)*(J-1))) := by ring
  rw [E]
  exact mul_nonneg (sq_nonneg _) (mul_nonneg (mul_nonneg (plateauSpectralCoeff_nonneg _) (H L hL)) (H J hJ))

#print axioms actualLowSpectrum_inner_eq
#print axioms shifted_harmonic_product_nonneg

end CenteredCubeSqrt
