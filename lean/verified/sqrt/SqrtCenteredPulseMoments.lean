import SqrtPulseTrainMeans

namespace CenteredCubeSqrt

open MeasureTheory
open scoped BigOperators Interval

theorem intervalIntegrable_finset_lam {ι : Type*} (s : Finset ι) {f : ι → ℝ → ℝ}
    (h : ∀ i ∈ s, IntervalIntegrable (f i) volume 0 1) :
    IntervalIntegrable (fun x => ∑ i ∈ s, f i x) volume 0 1 := by
  rw [show (fun x => ∑ i ∈ s, f i x) = (∑ i ∈ s, f i) from by
    funext x
    simp only [Finset.sum_apply] ]
  exact IntervalIntegrable.sum s h

theorem atomPulseTrain_intervalIntegrable {B K : ℕ} [NeZero K] (f : ZMod K → Fin B)
    (eps s t C a : ℝ) (he : 0 < eps) :
    IntervalIntegrable (atomPulseTrain f eps s t C a) volume 0 1 := by
  unfold atomPulseTrain
  exact intervalIntegrable_finset_lam Finset.univ fun j _ =>
    periodicWindowPulse_intervalIntegrable _ _ _ _ _ he

theorem atomPulseTrain_mul_intervalIntegrable {B K : ℕ} [NeZero K] (f : ZMod K → Fin B)
    (eps s t s' t' C a b : ℝ) (he : 0 < eps) :
    IntervalIntegrable (fun x => atomPulseTrain f eps s t C a x *
      atomPulseTrain f eps s' t' C b x) volume 0 1 := by
  have hpt : (fun x => atomPulseTrain f eps s t C a x * atomPulseTrain f eps s' t' C b x) =
      fun x => ∑ j : ZMod K, ∑ l : ZMod K,
        periodicWindowPulse eps s t C (x-(paperAtomCenter f j+a)) *
        periodicWindowPulse eps s' t' C (x-(paperAtomCenter f l+b)) := by
    funext x
    unfold atomPulseTrain
    rw [Finset.sum_mul]
    simp_rw [Finset.mul_sum]
  rw [hpt]
  apply intervalIntegrable_finset_lam
  intro j _
  apply intervalIntegrable_finset_lam
  intro l _
  exact shifted_periodic_pulse_mul_integrable _ _ _ _ _ _ _ _ he

theorem period_one_centered_product {f g : ℝ → ℝ} {a b : ℝ}
    (hf : IntervalIntegrable f volume 0 1) (hg : IntervalIntegrable g volume 0 1)
    (hfg : IntervalIntegrable (fun x => f x*g x) volume 0 1)
    (hfa : (∫ x in (0:ℝ)..1, f x)=a)
    (hgb : (∫ x in (0:ℝ)..1, g x)=b) :
    (∫ x in (0:ℝ)..1, (f x-a)*(g x-b)) =
      (∫ x in (0:ℝ)..1, f x*g x) - a*b := by
  have e (x : ℝ) : (f x-a)*(g x-b) = (f x*g x-b*f x)-(a*g x-a*b) := by ring
  simp_rw [e]
  rw [intervalIntegral.integral_sub (hfg.sub (hf.const_mul _))
    ((hg.const_mul _).sub intervalIntegrable_const)]
  rw [intervalIntegral.integral_sub hfg (hf.const_mul _),
    intervalIntegral.integral_sub (hg.const_mul _) intervalIntegrable_const,
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const,hfa,hgb]
  norm_num
  ring

/-- Expand the four periodic pulse correlations of the two centered
boundary families. The last term is the product of the exact means. -/
theorem period_one_two_family_covariance {A B C D : ℝ → ℝ} {m n : ℝ}
    (hA : IntervalIntegrable A volume 0 1) (hB : IntervalIntegrable B volume 0 1)
    (hC : IntervalIntegrable C volume 0 1) (hD : IntervalIntegrable D volume 0 1)
    (hAC : IntervalIntegrable (fun x => A x*C x) volume 0 1)
    (hAD : IntervalIntegrable (fun x => A x*D x) volume 0 1)
    (hBC : IntervalIntegrable (fun x => B x*C x) volume 0 1)
    (hBD : IntervalIntegrable (fun x => B x*D x) volume 0 1)
    (hm : (∫ x in (0:ℝ)..1, A x+B x)=m) (hn : (∫ x in (0:ℝ)..1, C x+D x)=n) :
    (∫ x in (0:ℝ)..1, (A x+B x-m)*(C x+D x-n)) =
      (∫ x in (0:ℝ)..1, A x*C x)+(∫ x in (0:ℝ)..1, B x*D x) +
      (∫ x in (0:ℝ)..1, B x*C x)+(∫ x in (0:ℝ)..1, A x*D x)-m*n := by
  have e (x : ℝ) : (A x+B x)*(C x+D x) =
      (A x*C x + B x*D x)+(B x*C x+A x*D x) := by ring
  have hi : IntervalIntegrable (fun x => (A x+B x)*(C x+D x)) volume 0 1 := by
    simp_rw [e]
    exact (hAC.add hBD).add (hBC.add hAD)
  rw [period_one_centered_product (hA.add hB) (hC.add hD) hi hm hn]
  simp_rw [e]
  rw [intervalIntegral.integral_add (hAC.add hBD) (hBC.add hAD),
    intervalIntegral.integral_add hAC hBD, intervalIntegral.integral_add hBC hAD]
  ring

#print axioms period_one_two_family_covariance

end CenteredCubeSqrt
