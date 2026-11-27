import SqrtAtomicWindowCovariance
import SqrtActualAtomDiscrepancy

namespace CenteredCubeSqrt

open MeasureTheory
open scoped BigOperators Interval

theorem atomPulseTrain_nonneg {B K : ℕ} [NeZero K] (f : ZMod K → Fin B)
    {eps : ℝ} (he : 0<eps) (s t C a x : ℝ) :
    0≤atomPulseTrain f eps s t C a x := by
  unfold atomPulseTrain periodicWindowPulse
  exact Finset.sum_nonneg fun _ _ => (smoothedWindowPulse_bounds he).1

theorem atomicWindowIncrement_continuous {B K : ℕ} [NeZero K] (f : ZMod K → Fin B)
    {eps v L0 s t : ℝ} (he : 0<eps) (hv : 0<v) :
    Continuous (atomicWindowIncrement f eps v L0 s t) := by
  have hK : 0<(K:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne K)
  have hd : 0<eps/((K:ℝ)*v) := by positivity
  exact (actualAtomicWindow_continuous f hd _).sub (actualAtomicWindow_continuous f hd _)

/-- The actual atomic increment's L¹ bound. Its center-subtraction doubles
the pulse mass but introduces no dependence on K or B in the constant. -/
theorem actual_atomic_increment_L1 {B K : ℕ} [NeZero K] (f : ZMod K → Fin B)
    {eps v T L0 s t : ℝ}
    (he : 0<eps) (hv : 0<v) (hT : 0≤T) (hm : (T+eps/2)/((K:ℝ)*v)<1/4)
    (hs : -T≤s) (hst : s≤t) (ht : t≤T) :
    (∫ x in (0:ℝ)..1, |atomicWindowIncrement f eps v L0 s t x|) ≤ 4*(t-s)/v := by
  let C := (K:ℝ)*v
  let A := atomPulseTrain f eps (-t) (-s) C (-L0/2)
  let B0 := atomPulseTrain f eps s t C (L0/2)
  let m := 2*(K:ℝ)*(t-s)/C
  have hK : 0<(K:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne K)
  have hC : 0<C := mul_pos hK hv
  have exp (x : ℝ) : atomicWindowIncrement f eps v L0 s t x=A x+B0 x-m :=
    actualAtomicWindow_increment f he hC hT hm hs hst ht
  have hpt (x : ℝ) : |atomicWindowIncrement f eps v L0 s t x| ≤ A x+B0 x+m := by
    have hA : 0≤A x := atomPulseTrain_nonneg f he _ _ _ _ _
    have hB : 0≤B0 x := atomPulseTrain_nonneg f he _ _ _ _ _
    have hm0 : 0≤m := by dsimp [m]; positivity
    rw [exp]
    exact (abs_sub _ _).trans (by rw [abs_of_nonneg (by linarith),abs_of_nonneg hm0])
  have hAInt : IntervalIntegrable A volume 0 1 :=
    atomPulseTrain_intervalIntegrable f _ _ _ _ _ he
  have hBInt : IntervalIntegrable B0 volume 0 1 :=
    atomPulseTrain_intervalIntegrable f _ _ _ _ _ he
  have hl := (atomicWindowIncrement_continuous f (L0:=L0) (s:=s) (t:=t) he hv).abs
  have hd := intervalIntegral.integral_mono (a:=0) (b:=1) (by norm_num)
    (hl.intervalIntegrable (μ:=volume) _ _) ((hAInt.add hBInt).add intervalIntegrable_const) hpt
  apply hd.trans_eq
  rw [intervalIntegral.integral_add (hAInt.add hBInt) intervalIntegrable_const,
    intervalIntegral.integral_add hAInt hBInt,intervalIntegral.integral_const]
  unfold A B0
  rw [atomPulseTrain_mean f he hC hm
        (show -(T+eps/2) ≤ -t-eps/2 by linarith)
        (show -s+eps/2 ≤ T+eps/2 by linarith) (show -t≤-s by linarith),
      atomPulseTrain_mean f he hC hm
        (show -(T+eps/2) ≤ s-eps/2 by linarith)
        (show t+eps/2 ≤ T+eps/2 by linarith) hst]
  simp only [sub_zero,one_smul]
  unfold m C
  field_simp
  ring

#print axioms actual_atomic_increment_L1

end CenteredCubeSqrt
