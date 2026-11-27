import SqrtActualAtomicIncrement
import SqrtLocalLowSpectrum
import Average

namespace CenteredCubeSqrt

open MeasureTheory
open scoped BigOperators Interval

noncomputable def actualLowDensity (M : ℕ) (x : ℝ) : ℝ :=
  ∑ m ∈ Finset.range M, (Real.pi*((m:ℝ)+1)*lowSpectrumAmp m) *
    Real.cos (((m:ℝ)+1)*(2*Real.pi)*x)

theorem actualLowDensity_continuous (M : ℕ) : Continuous (actualLowDensity M) := by
  unfold actualLowDensity
  fun_prop

theorem actualLowDensity_window (M : ℕ) {L : ℝ} (hL : 0<L) (x : ℝ) :
    (∫ y in x-L/2..x+L/2, actualLowDensity M y) = actualLowSpectrum M L x := by
  let a (m : ℕ) := Real.pi*((m:ℝ)+1)*lowSpectrumAmp m
  have h := CenteredCube.RudinDensity.integral_cos_sum_shift (K:=M) (M:=1) (by decide) a x L hL
  have e (y : ℝ) : actualLowDensity M y =
      ∑ m ∈ Finset.range M, a m * Real.cos (((1+m:ℕ):ℝ)*(2*Real.pi)*y) := by
    unfold actualLowDensity a
    simp only [Nat.cast_add,Nat.cast_one,add_comm (1:ℝ)]
  simp_rw [e]
  rw [h]
  unfold actualLowSpectrum
  apply Finset.sum_congr rfl
  intro m _
  simp only [a,Nat.cast_add,Nat.cast_one,add_comm (1:ℝ)]
  have he : Real.pi*((m:ℝ)+1)=((m:ℝ)+1)*Real.pi := mul_comm _ _
  rw [he]
  have hNZ : ((m:ℝ)+1)*Real.pi ≠ 0 := by positivity
  field_simp

/-- Actual periodic witness density from the √n manuscript. -/
noncomputable def actualWitnessDensity {B K : ℕ} [NeZero K] (f : ZMod K → Fin B)
    (M : ℕ) (p delta x : ℝ) : ℝ :=
  1-p+(p/(K:ℝ))*(∑ j : ZMod K, periodicBoxDensity delta (paperAtomCenter f j) x)+
    (p/(K:ℝ))*actualLowDensity M x

noncomputable def actualWindowPerturbation {B K : ℕ} [NeZero K] (f : ZMod K → Fin B)
    (M : ℕ) (p delta L x : ℝ) : ℝ :=
  (∫ y in x-L/2..x+L/2, actualWitnessDensity f M p delta y)/L-1

/-- Exact algebra linking the proof's local perturbations to integration of
the actual nonnegative background/box/Fourier witness density. -/
theorem actualWindowPerturbation_formula {B K : ℕ} [NeZero K] (f : ZMod K → Fin B)
    (M : ℕ) (p : ℝ) {delta L : ℝ} (hδ : 0<delta) (hL : 0<L) (x : ℝ) :
    actualWindowPerturbation f M p delta L x =
      (p/((K:ℝ)*L))*(actualAtomicWindow f delta L x+actualLowSpectrum M L x) := by
  have hboxes : IntervalIntegrable (fun x =>
      ∑ j : ZMod K, periodicBoxDensity delta (paperAtomCenter f j) x) volume (x-L/2) (x+L/2) := by
    rw [show (fun u => ∑ j : ZMod K, periodicBoxDensity delta (paperAtomCenter f j) u) =
        (∑ j : ZMod K, periodicBoxDensity delta (paperAtomCenter f j)) from by
      funext u
      simp only [Finset.sum_apply] ]
    exact IntervalIntegrable.sum Finset.univ (fun (j:ZMod K) _ =>
      periodicBoxDensity_intervalIntegrable delta (paperAtomCenter f j) (x-L/2) (x+L/2) hδ)
  have hLow := (actualLowDensity_continuous M).intervalIntegrable (μ:=volume) (x-L/2) (x+L/2)
  unfold actualWindowPerturbation actualWitnessDensity
  rw [intervalIntegral.integral_add (intervalIntegrable_const.add (hboxes.const_mul _)) (hLow.const_mul _),
    intervalIntegral.integral_add intervalIntegrable_const (hboxes.const_mul _),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
    actualLowDensity_window M hL, intervalIntegral.integral_finsetSum]
  · unfold actualAtomicWindow
    rw [smul_eq_mul]
    have hKn : (K:ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne K)
    field_simp
    ring
  · intro j _
    exact periodicBoxDensity_intervalIntegrable delta (paperAtomCenter f j) (x-L/2) (x+L/2) hδ

noncomputable def actualWindowRemainder {B K : ℕ} [NeZero K] (f : ZMod K → Fin B)
    (M : ℕ) (p eps v L0 s t x : ℝ) : ℝ :=
  let C := (K:ℝ)*v
  let Ls := localLength L0 C s
  let Lt := localLength L0 C t
  let Hs := actualAtomicWindow f (eps/C) Ls x
  let Ht := actualAtomicWindow f (eps/C) Lt x
  let Bs := actualLowSpectrum M Ls x
  let Bt := actualLowSpectrum M Lt x
  (p/(K:ℝ))*((Bt-Bs)/L0+(1/Lt-1/L0)*(Ht+Bt)-(1/Ls-1/L0)*(Hs+Bs))

/-- Density/window-to-atom formula plus literal denominator and Fourier
remainder, no orthogonality assumed between them and the atom term. -/
theorem actualWindowIncrement_atomic_remainder {B K : ℕ} [NeZero K]
    (f : ZMod K → Fin B) (M : ℕ) (p : ℝ) {eps v L0 s t : ℝ}
    (he : 0<eps) (hv : 0<v) (hL0 : 0<L0)
    (hs : 0<localLength L0 ((K:ℝ)*v) s) (ht : 0<localLength L0 ((K:ℝ)*v) t) (x : ℝ) :
  actualWindowPerturbation f M p (eps/((K:ℝ)*v)) (localLength L0 ((K:ℝ)*v) t) x -
  actualWindowPerturbation f M p (eps/((K:ℝ)*v)) (localLength L0 ((K:ℝ)*v) s) x =
    (p/((K:ℝ)*L0))*(actualAtomicWindow f (eps/((K:ℝ)*v)) (localLength L0 ((K:ℝ)*v) t) x -
      actualAtomicWindow f (eps/((K:ℝ)*v)) (localLength L0 ((K:ℝ)*v) s) x) +
    actualWindowRemainder f M p eps v L0 s t x := by
  have hK : 0 < (K:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne K)
  have hδ : 0<eps/((K:ℝ)*v) := by positivity
  rw [actualWindowPerturbation_formula f M p hδ ht, actualWindowPerturbation_formula f M p hδ hs]
  unfold actualWindowRemainder
  field_simp
  ring

#print axioms actualWindowPerturbation_formula
#print axioms actualWindowIncrement_atomic_remainder

end CenteredCubeSqrt
