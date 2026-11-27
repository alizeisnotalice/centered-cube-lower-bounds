import SqrtAtomResidue
import Mathlib.MeasureTheory.Function.Floor

namespace CenteredCubeSqrt

open MeasureTheory
open scoped BigOperators Interval
open Classical

theorem periodicWindowPulse_measurable (eps s t C : ℝ) :
    Measurable (periodicWindowPulse eps s t C) := by
  have hfloor : Measurable (fun x : ℝ => (⌊x+1/2⌋:ℝ)) :=
    (Measurable.of_discrete (f:=fun z : ℤ => (z:ℝ))).comp <|
      (measurable_id.add_const (1/2:ℝ)).floor
  unfold periodicWindowPulse centeredPeriodRep
  exact (smoothedWindowPulse_continuous eps s t).measurable.comp
    (measurable_const.mul (measurable_id.sub hfloor))

theorem shifted_periodic_pulse_mul_integrable (eps s t s' t' C a b : ℝ) (he : 0 < eps) :
    IntervalIntegrable
      (fun x => periodicWindowPulse eps s t C (x-a)*periodicWindowPulse eps s' t' C (x-b))
      volume 0 1 := by
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le (show (0:ℝ) ≤ 1 by norm_num)).2
  have hm := ((periodicWindowPulse_measurable eps s t C).comp (measurable_id.sub_const a)).mul
    ((periodicWindowPulse_measurable eps s' t' C).comp (measurable_id.sub_const b))
  apply Measure.integrableOn_of_bounded (M:=1) (s_finite:=by simp [Real.volume_Ioc]) hm.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro x
  have hb1 := smoothedWindowPulse_bounds (s:=s) (t:=t) (x:=C*centeredPeriodRep (x-a)) he
  have hb2 := smoothedWindowPulse_bounds (s:=s') (t:=t') (x:=C*centeredPeriodRep (x-b)) he
  change ‖smoothedWindowPulse eps s t (C*centeredPeriodRep (x-a)) *
           smoothedWindowPulse eps s' t' (C*centeredPeriodRep (x-b))‖ ≤ (1:ℝ)
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hb1.1 hb2.1)]
  exact (mul_le_of_le_one_right hb1.1 hb2.2).trans hb1.2

/-- One of the two translated pulse families in the actual local window. -/
noncomputable def atomPulseTrain {B K : ℕ} [NeZero K] (f : ZMod K → Fin B)
    (eps s t C offset x : ℝ) : ℝ :=
  ∑ j : ZMod K, periodicWindowPulse eps s t C (x-(paperAtomCenter f j+offset))

/-- The actual empirical pulse-family correlation is the exact normalized
sum over physical difference bins counted in paperphysicalcount. -/
theorem atomPulseTrain_correlation {B K : ℕ} [NeZero K] [NeZero (B*K)]
    (f : ZMod K → Fin B) {eps s t s' t' C M a b : ℝ}
    (he : 0 < eps) (hC : 0 < C) (hm : M/C < 1/4)
    (hs : -M ≤ s-eps/2) (ht : t+eps/2 ≤ M)
    (hs' : -M ≤ s'-eps/2) (ht' : t'+eps/2 ≤ M) :
    (∫ x in (0:ℝ)..1, atomPulseTrain f eps s t C a x * atomPulseTrain f eps s' t' C b x) =
      (1/C) * ∑ r : ZMod (B*K),
        ((circularAtomHits f (atomResidueLift (b-a) r)).card : ℝ) *
        pulseOverlap eps s t s' t' (C*((atomResidueLift (b-a) r : ℝ)/((B:ℝ)*K)+(b-a))) := by
  let F (p : ZMod K × ZMod K) (x : ℝ) := periodicWindowPulse eps s t C (x-(paperAtomCenter f p.1+a)) *
      periodicWindowPulse eps s' t' C (x-(paperAtomCenter f p.2+b))
  have hp (x : ℝ) : atomPulseTrain f eps s t C a x * atomPulseTrain f eps s' t' C b x =
      ∑ p : ZMod K × ZMod K, F p x := by
    unfold atomPulseTrain F
    rw [Finset.sum_mul, Fintype.sum_prod_type]
    simp_rw [Finset.mul_sum]
  simp_rw [hp]
  rw [intervalIntegral.integral_finsetSum]
  · let ker (r : ZMod (B*K)) : ℝ :=
      pulseOverlap eps s t s' t' (C*((atomResidueLift (b-a) r : ℝ)/((B:ℝ)*K)+(b-a)))
    have int (p : ZMod K × ZMod K) : (∫ x in (0:ℝ)..1, F p x) =
        (1/C)*ker (atomDifferenceResidue f p) := by
      unfold F ker
      rw [periodic_two_centers_overlap he hC hm hs ht hs' ht',
        show paperAtomCenter f p.2+b-(paperAtomCenter f p.1+a) =
          paperAtomCenter f p.2-paperAtomCenter f p.1+(b-a) by ring,
        paperAtom_diff_centeredRep]
    simp_rw [int, ← Finset.mul_sum]
    exact congrArg (fun y => (1/C)*y) (sum_atom_difference_residue_kernel f (b-a) ker)
  · intro p _
    exact shifted_periodic_pulse_mul_integrable _ _ _ _ _ _ _ _ he

#print axioms atomPulseTrain_correlation

end CenteredCubeSqrt
