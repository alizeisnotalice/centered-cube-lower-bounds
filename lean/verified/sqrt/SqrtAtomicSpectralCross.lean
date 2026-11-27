import SqrtActualWindowHarmonic

namespace CenteredCubeSqrt
open MeasureTheory Set
open scoped Interval BigOperators
set_option maxHeartbeats 1500000

theorem periodInner_comm (f g : ℝ → ℝ) : periodInner f g=periodInner g f := by
  unfold periodInner
  simp only [mul_comm]

theorem actual_atomic_spectral_cross_expression {B K : ℕ} [NeZero K] (f : ZMod K → Fin B)
    (M : ℕ) {δ L J : ℝ} (hδ0 : 0<δ) (hδ1 : δ<1) (hL : 0≤L) :
    periodInner (actualAtomicWindow f δ L) (actualLowSpectrum M J) =
      ∑ k ∈ Finset.range M, lowSpectrumAmp k*atomHarmonicCoefficient f δ (k+1)*
        Real.sin (Real.pi*((k:ℝ)+1)*L)*Real.sin (Real.pi*((k:ℝ)+1)*J) := by
  let H := actualAtomicWindow f δ L
  let A (k : ℕ) := lowSpectrumAmp k*Real.sin (((k:ℝ)+1)*Real.pi*J)
  let C (k : ℕ) (x : ℝ) := Real.cos (2*Real.pi*((k:ℝ)+1)*x)
  have hH := actualAtomicWindow_continuous f hδ0 L
  have hC (k : ℕ) : Continuous (C k) := by unfold C; fun_prop
  have eq (x : ℝ) : H x*actualLowSpectrum M J x =
      ∑ k ∈ Finset.range M, A k*(H x*C k x) := by
    unfold actualLowSpectrum
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    unfold A C
    rw [show ((k:ℝ)+1)*(2*Real.pi)*x=2*Real.pi*((k:ℝ)+1)*x by ring]
    ring
  unfold periodInner
  change (∫ x in (0:ℝ)..1, H x*actualLowSpectrum M J x)=_
  simp_rw [eq]
  rw [intervalIntegral.integral_finsetSum]
  · refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [intervalIntegral.integral_const_mul]
    have h := actual_atomic_window_harmonic f hδ0 hδ1 hL (m:=k+1) (by omega)
    push_cast at h
    change A k*(∫ x in (0:ℝ)..1,H x*C k x)=_
    rw [show (∫ x in (0:ℝ)..1, H x*C k x) =
      atomHarmonicCoefficient f δ (k+1)*Real.sin (Real.pi*((k:ℝ)+1)*L) from h]
    unfold A
    rw [show ((k:ℝ)+1)*Real.pi*J = Real.pi*((k:ℝ)+1)*J by ring]
    ring
  · intro k _
    exact ((hH.mul (hC k)).const_mul _).intervalIntegrable _ _

noncomputable def manuscriptCrossError (B K : ℝ) (M : ℕ) : ℝ :=
  (40/9)*(((1-1/B)*Real.sqrt (K+1)/K)*
    (∑ k ∈ Finset.range M, 1/((k:ℝ)+1)^2) +
    (Real.pi*(1-1/B)^2/(2*K))*(∑ k ∈ Finset.range M, 1/((k:ℝ)+1)))

theorem actual_atomic_spectral_cross_bound {b d : ℕ} [NeZero (2^d-1)] (hd : 0<d)
    (g : (LabelField d)ˣ) (hg : orderOf g=2^d-1) (t : Fin b → LabelField d)
    (ht : ∀ i,t i≠0) (M : ℕ) (hM : M<2^d-1)
    {δ L J : ℝ} (hδ0 : 0<δ) (hδ1 : δ<1) (hL : 0≤L) (hJ : 0≤J) :
    let f := ordinalPhaseLabel hd g hg t
    |periodInner (actualAtomicWindow f δ L) (actualLowSpectrum M J)+
      periodInner (actualLowSpectrum M L) (actualAtomicWindow f δ J)| ≤
      manuscriptCrossError ((2:ℝ)^b) (((2^d-1:ℕ):ℝ)) M := by
  let f := ordinalPhaseLabel hd g hg t
  let B : ℝ := (2:ℝ)^b
  let K := ((2^d-1:ℕ):ℝ)
  let A := 1-1/B
  let D := A*Real.sqrt (K+1)/K
  let E := Real.pi*A^2/(2*K)
  have hk : 0<K := by dsimp [K]; exact_mod_cast (show 0<(2^d-1:ℕ) by omega)
  have hb : 1≤B := by dsimp [B]; exact one_le_pow₀ (by norm_num)
  have ha : 0≤A := by dsimp [A]; linarith [(div_le_one (by linarith : 0<B)).mpr hb]
  have hD : 0≤D := by dsimp [D]; positivity
  have hE : 0≤E := by dsimp [E]; positivity
  change |periodInner (actualAtomicWindow f δ L) (actualLowSpectrum M J)+
    periodInner (actualLowSpectrum M L) (actualAtomicWindow f δ J)| ≤ _
  rw [periodInner_comm (actualLowSpectrum M L),
    actual_atomic_spectral_cross_expression f M hδ0 hδ1 hL,
    actual_atomic_spectral_cross_expression f M hδ0 hδ1 hJ]
  rw [←Finset.sum_add_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm (k : ℕ) (hkM : k ∈ Finset.range M) :
    |lowSpectrumAmp k*atomHarmonicCoefficient f δ (k+1)*
        Real.sin (Real.pi*((k:ℝ)+1)*L)*Real.sin (Real.pi*((k:ℝ)+1)*J)+
      lowSpectrumAmp k*atomHarmonicCoefficient f δ (k+1)*
        Real.sin (Real.pi*((k:ℝ)+1)*J)*Real.sin (Real.pi*((k:ℝ)+1)*L)| ≤
    (40/9)*(D*(1/((k:ℝ)+1)^2)+E*(1/((k:ℝ)+1))) := by
    let q := (k:ℝ)+1
    have hq : 0<q := by dsimp [q]; positivity
    have hm : k+1<2^d-1 := by have := Finset.mem_range.mp hkM; omega
    have hp := paper_atom_Fourier_coefficient hd g hg t ht (m:=k+1) (by omega) hm
    have hp' : |atomCosineMoment f (k+1)|/(Real.pi*q) ≤ D+E*q := by
      rw [atomCosineMoment_re]
      simp only [Nat.cast_succ] at hp
      refine hp.trans_eq ?_
      dsimp [D,E,A,B,K,q]
      ring
    have hcoef : |atomHarmonicCoefficient f δ (k+1)|≤D+E*q := by
      unfold atomHarmonicCoefficient
      rw [abs_mul,abs_div,abs_of_nonneg (by positivity : 0≤Real.pi*((k+1:ℕ):ℝ))]
      have hx := mul_le_of_le_one_left
        (show 0≤|atomCosineMoment f (k+1)|/(Real.pi*((k+1:ℕ):ℝ)) by positivity)
        (actualBoxSinc_abs_le hδ0 (m:=k+1) (by omega))
      exact hx.trans (by simpa only [q,Nat.cast_succ] using hp')
    have hAmp : lowSpectrumAmp k≤20/(9*q^2) :=
      (plateauCoeff_amplitude q hq).le
    have hAmp0 : 0≤lowSpectrumAmp k := Real.sqrt_nonneg _
    have ht' (X Y : ℝ) :
        |lowSpectrumAmp k*atomHarmonicCoefficient f δ (k+1)*
          Real.sin (Real.pi*q*X)*Real.sin (Real.pi*q*Y)| ≤
        (20/(9*q^2))*(D+E*q) := by
      simp only [abs_mul,abs_of_nonneg hAmp0]
      calc
        _ ≤ lowSpectrumAmp k * |atomHarmonicCoefficient f δ (k+1)| * |Real.sin (Real.pi*q*X)| :=
          mul_le_of_le_one_right (by positivity) (Real.abs_sin_le_one _)
        _ ≤ lowSpectrumAmp k * |atomHarmonicCoefficient f δ (k+1)| :=
          mul_le_of_le_one_right (by positivity) (Real.abs_sin_le_one _)
        _ ≤ _ := mul_le_mul hAmp hcoef (abs_nonneg _) (by positivity)
    refine (abs_add_le _ _).trans ((add_le_add (ht' L J) (ht' J L)).trans_eq ?_)
    change _=(40/9)*(D*(1/q^2)+E*(1/q))
    field_simp [hq.ne']
    ring
  refine (Finset.sum_le_sum hterm).trans_eq ?_
  rw [←Finset.mul_sum,Finset.sum_add_distrib,←Finset.mul_sum,←Finset.mul_sum]
  rfl

#print axioms actual_atomic_spectral_cross_expression
#print axioms actual_atomic_spectral_cross_bound

end CenteredCubeSqrt
