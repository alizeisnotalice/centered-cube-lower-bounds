import SqrtPeriodL2

namespace CenteredCubeSqrt

open MeasureTheory
open scoped Interval

theorem periodL2Sq_add {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) :
    periodL2Sq (fun x => f x+g x) =
      periodL2Sq f+2*periodInner f g+periodL2Sq g := by
  unfold periodL2Sq periodInner
  have fi : IntervalIntegrable (fun x => (f x)^2) volume 0 1 := (hf.pow 2).intervalIntegrable _ _
  have gi : IntervalIntegrable (fun x => (g x)^2) volume 0 1 := (hg.pow 2).intervalIntegrable _ _
  have ci : IntervalIntegrable (fun x => f x*g x) volume 0 1 := (hf.mul hg).intervalIntegrable _ _
  have e (x : ℝ) : (f x+g x)^2 = (f x)^2+2*(f x*g x)+(g x)^2 := by ring
  simp_rw [e]
  rw [intervalIntegral.integral_add (fi.add (ci.const_mul 2)) gi,
    intervalIntegral.integral_add fi (ci.const_mul 2), intervalIntegral.integral_const_mul]

theorem periodL2Sq_add_error {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    {z : ℝ} (hz : 0<z) :
    |periodL2Sq (fun x => f x+g x)-periodL2Sq f| ≤
      z*periodL2Sq f+(1+1/z)*periodL2Sq g := by
  have hh := abs_periodInner_young hf hg hz
  rw [periodL2Sq_add hf hg,show periodL2Sq f+2*periodInner f g+periodL2Sq g-periodL2Sq f =
    2*periodInner f g+periodL2Sq g by ring]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤2),
    abs_of_nonneg (periodL2Sq_nonnegative _)]
  linarith

theorem abs_periodInner_uniform_L1 {f g : ℝ → ℝ} {A : ℝ} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ x, |f x|≤A) :
    |periodInner f g| ≤ A*(∫ x in (0:ℝ)..1, |g x|) := by
  have hfg : IntervalIntegrable (fun x => f x*g x) volume 0 1 := (hf.mul hg).intervalIntegrable _ _
  have hA : IntervalIntegrable (fun x => A*|g x|) volume 0 1 :=
    (hg.abs.const_mul A).intervalIntegrable _ _
  have h' (x : ℝ) : |f x*g x| ≤ A*|g x| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (h x) (abs_nonneg _)
  have hAn : IntervalIntegrable (fun x => -(A*|g x|)) volume 0 1 := hA.neg
  have e1 := intervalIntegral.integral_mono (a:=0) (b:=1) (by norm_num) hAn hfg
    (fun x => (abs_le.mp (h' x)).1)
  have e2 := intervalIntegral.integral_mono (a:=0) (b:=1) (by norm_num) hfg hA
    (fun x => (abs_le.mp (h' x)).2)
  rw [intervalIntegral.integral_neg,intervalIntegral.integral_const_mul] at e1
  rw [intervalIntegral.integral_const_mul] at e2
  exact abs_le.mpr ⟨e1,e2⟩

#print axioms periodL2Sq_add_error
#print axioms abs_periodInner_uniform_L1

end CenteredCubeSqrt
