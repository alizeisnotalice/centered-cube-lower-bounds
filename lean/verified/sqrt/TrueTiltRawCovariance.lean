import TrueTiltIncrement
import TrueTiltIntegratedMean

open MeasureTheory

namespace CubeSqrtProbability

theorem tilted_two_increment_product_pointwise
    {a w x y s t : ℝ} (ha : a ≤ 1/2) (hw : |w| ≤ a) (hx : |x| ≤ a)
    (hy : |y| ≤ a) (hs : |s| ≤ a) (ht : |t| ≤ a) :
    |(1+w)*(Real.log (1+y)-Real.log (1+x))*(Real.log (1+t)-Real.log (1+s)) -
       (y-x)*(t-s)| ≤ 5*a*((y-x)^2+(t-s)^2) := by
  let u := y-x
  let v := t-s
  let g := Real.log (1+y)-Real.log (1+x)
  let h := Real.log (1+t)-Real.log (1+s)
  have hg : |g| ≤ 2*|u| := true_log_increment_bound ha hx hy
  have hh : |h| ≤ 2*|v| := true_log_increment_bound ha hs ht
  have hgu : |g-u| ≤ 2*a*|u| := true_log_increment_error ha hx hy
  have hhv : |h-v| ≤ 2*a*|v| := true_log_increment_error ha hs ht
  have hA : 0 ≤ a := (abs_nonneg _).trans hw
  change |(1+w)*g*h-u*v| ≤ 5*a*(u^2+v^2)
  have he : (1+w)*g*h-u*v = w*g*h+(g-u)*h+u*(h-v) := by ring
  rw [he]
  calc
    _ ≤ |w*g*h+(g-u)*h| + |u*(h-v)| := abs_add_le _ _
    _ ≤ (|w*g*h| + |(g-u)*h|) + |u*(h-v)| :=
      add_le_add (abs_add_le _ _) (le_refl _)
    _ = (|w| * |g| * |h| + |g-u| * |h|) + |u| * |h-v| := by simp only [abs_mul]
    _ ≤ (a * (2*|u|) * (2*|v|) + (2*a*|u|) * (2*|v|)) + |u| * (2*a*|v|) := by
      gcongr
    _ = 5*a*(2*|u| * |v|) := by ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith [sq_nonneg (|u|-|v|), sq_abs u, sq_abs v]

end CubeSqrtProbability
#print axioms CubeSqrtProbability.tilted_two_increment_product_pointwise
