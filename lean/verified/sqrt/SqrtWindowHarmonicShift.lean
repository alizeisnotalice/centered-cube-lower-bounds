import SqrtPeriodicBoxHarmonic

namespace CenteredCubeSqrt

open MeasureTheory Set
open scoped Interval

theorem sine_integer_harmonic_periodic (m : ℕ) :
    Function.Periodic (fun x : ℝ => Real.sin (2*Real.pi*(m:ℝ)*x)) 1 := by
  intro x
  change Real.sin (2*Real.pi*(m:ℝ)*(x+1)) = Real.sin (2*Real.pi*(m:ℝ)*x)
  rw [show 2*Real.pi*(m:ℝ)*(x+1)=2*Real.pi*(m:ℝ)*x+(m:ℝ)*(2*Real.pi) by ring]
  exact Real.sin_add_nat_mul_two_pi _ _

theorem periodicBoxDensity_bounds {δ : ℝ} (hδ : 0<δ) (a x : ℝ) :
    0≤periodicBoxDensity δ a x ∧ periodicBoxDensity δ a x≤1/δ := by
  unfold periodicBoxDensity boxWindowDensity
  by_cases h : centeredPeriodRep (x-a) ∈ Icc (-δ/2) (δ/2)
  · simp [indicator_of_mem h,hδ.le]
  · simp [indicator_of_notMem h,hδ.le]

theorem box_harmonic_shift {δ : ℝ} (hδ : 0<δ) (a t : ℝ) (m : ℕ) :
    let c := 2*Real.pi*(m:ℝ)
    (∫ x in (0:ℝ)..1, periodicBoxDensity δ a (x+t)*Real.cos (c*x)) =
      Real.cos (c*t)*(∫ y in (0:ℝ)..1, periodicBoxDensity δ a y*Real.cos (c*y)) +
      Real.sin (c*t)*(∫ y in (0:ℝ)..1, periodicBoxDensity δ a y*Real.sin (c*y)) := by
  let c := 2*Real.pi*(m:ℝ)
  let f := periodicBoxDensity δ a
  let G (y : ℝ) := f y*Real.cos (c*y)
  let H (y : ℝ) := f y*Real.sin (c*y)
  have hG : IntervalIntegrable (fun y => G y) volume 0 1 := by
    apply (periodicBoxDensity_intervalIntegrable δ a 0 1 hδ).mul_continuousOn
    exact (Real.continuous_cos.comp (continuous_const.mul continuous_id)).continuousOn
  have hH : IntervalIntegrable (fun y => H y) volume 0 1 := by
    apply (periodicBoxDensity_intervalIntegrable δ a 0 1 hδ).mul_continuousOn
    exact (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
  let J (y : ℝ) := f y*Real.cos (c*(y-t))
  have he : (fun x => f (x+t)*Real.cos (c*x)) = fun x => J (x+t) := by
    funext x
    simp only [J,add_sub_cancel_right]
  change (∫ x in (0:ℝ)..1, f (x+t)*Real.cos (c*x)) = _
  rw [he,intervalIntegral.integral_comp_add_right,zero_add,add_comm (1:ℝ)]
  have hJ : Function.Periodic J 1 := by
    intro y
    change f (y+1)*Real.cos (c*(y+1-t)) = f y*Real.cos (c*(y-t))
    have hf : f (y+1)=f y := (periodicBoxDensity_periodic δ a) y
    have hc : Real.cos (c*((y-t)+1))=Real.cos (c*(y-t)) :=
      (cosine_integer_harmonic_periodic m) (y-t)
    rw [hf,show y+1-t=(y-t)+1 by ring,hc]
  rw [hJ.intervalIntegral_add_eq t 0,zero_add]
  have hy (y : ℝ) : J y=Real.cos (c*t)*G y+Real.sin (c*t)*H y := by
    unfold J G H
    rw [mul_sub,Real.cos_sub]
    ring
  simp_rw [hy]
  rw [intervalIntegral.integral_add (hG.const_mul _) (hH.const_mul _),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul]

#print axioms box_harmonic_shift

end CenteredCubeSqrt
