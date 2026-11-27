import SqrtActualDensityWindow

namespace CenteredCubeSqrt

open MeasureTheory
open scoped BigOperators Interval

noncomputable def periodL2Sq (f : ℝ → ℝ) : ℝ := ∫ x in (0:ℝ)..1, (f x)^2
noncomputable def periodInner (f g : ℝ → ℝ) : ℝ := ∫ x in (0:ℝ)..1, f x*g x

theorem periodL2Sq_nonnegative (f : ℝ → ℝ) : 0≤periodL2Sq f := by
  unfold periodL2Sq
  exact intervalIntegral.integral_nonneg_of_forall (by norm_num) (fun x => sq_nonneg _)

theorem periodL2Sq_mul_const (f : ℝ → ℝ) (c : ℝ) :
    periodL2Sq (fun x => c*f x) = c^2*periodL2Sq f := by
  unfold periodL2Sq
  simp_rw [mul_pow]
  rw [intervalIntegral.integral_const_mul]

theorem periodL2Sq_le_uniform {f : ℝ → ℝ} (hf : Continuous f) {A : ℝ}
    (_hA : 0≤A) (hb : ∀ x, |f x|≤A) :
    periodL2Sq f≤A^2 := by
  unfold periodL2Sq
  have h := intervalIntegral.integral_mono (a:=0) (b:=1) (by norm_num)
    ((hf.pow 2).intervalIntegrable (μ:=volume) _ _)
    (intervalIntegrable_const (c:=A^2)) (fun x => by
      have h0 := pow_le_pow_left₀ (abs_nonneg _) (hb x) 2
      simpa [sq_abs] using h0)
  simpa using h

theorem periodL2Sq_three_sum {f g h : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g) (hh : Continuous h) :
    periodL2Sq (fun x => f x+g x+h x) ≤ 3*(periodL2Sq f+periodL2Sq g+periodL2Sq h) := by
  have fi : IntervalIntegrable (fun x => (f x)^2) volume 0 1 := (hf.pow 2).intervalIntegrable _ _
  have gi : IntervalIntegrable (fun x => (g x)^2) volume 0 1 := (hg.pow 2).intervalIntegrable _ _
  have hi : IntervalIntegrable (fun x => (h x)^2) volume 0 1 := (hh.pow 2).intervalIntegrable _ _
  have e := intervalIntegral.integral_mono (a:=0) (b:=1) (by norm_num)
    ((((hf.add hg).add hh).pow 2).intervalIntegrable (μ:=volume) _ _)
    (((fi.add gi).add hi).const_mul 3) (fun x => by
      change (f x+g x+h x)^2 ≤ 3*((f x)^2+(g x)^2+(h x)^2)
      nlinarith [sq_nonneg (f x-g x),sq_nonneg (f x-h x),sq_nonneg (g x-h x)])
  simp only [periodL2Sq]
  rw [← intervalIntegral.integral_add fi gi,
    ← intervalIntegral.integral_add (fi.add gi) hi,
    ← intervalIntegral.integral_const_mul]
  exact e

/-- Quantitative cross-term control. This form avoids needing to
introduce any extra normalized random variable or orthogonality. -/
theorem abs_periodInner_young {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    {z : ℝ} (hz : 0<z) :
    |periodInner f g| ≤ (z*periodL2Sq f+(1/z)*periodL2Sq g)/2 := by
  have point (x : ℝ) : |f x*g x|≤(z*(f x)^2+(1/z)*(g x)^2)/2 := by
    have h := sq_nonneg (z*|f x|-|g x|)
    apply (le_div_iff₀ (show (0:ℝ)<2 by norm_num)).mpr
    apply (le_of_mul_le_mul_left _ hz)
    have e1 : |f x*g x| = |f x| * |g x| := abs_mul _ _
    have e2 : z*(z*(f x)^2 + 1/z*(g x)^2) = z^2*(f x)^2+(g x)^2 := by
      field_simp
    rw [e2,e1]
    nlinarith [sq_abs (f x), sq_abs (g x)]
  let F := fun x => (z*(f x)^2+(1/z)*(g x)^2)/2
  have ff : Continuous F := by
    dsimp [F]
    fun_prop
  have hFG : IntervalIntegrable (fun x => f x*g x) volume 0 1 := (hf.mul hg).intervalIntegrable _ _
  have hFI := ff.intervalIntegrable (μ:=volume) (0:ℝ) 1
  have hFIneg : IntervalIntegrable (fun x => -F x) volume 0 1 := hFI.neg
  have L := intervalIntegral.integral_mono (a:=0) (b:=1) (by norm_num) hFIneg hFG
    (fun x => (abs_le.mp (point x)).1)
  have U := intervalIntegral.integral_mono (a:=0) (b:=1) (by norm_num) hFG hFI
    (fun x => (abs_le.mp (point x)).2)
  have e : (∫ x in (0:ℝ)..1, F x) = (z*periodL2Sq f+(1/z)*periodL2Sq g)/2 := by
    have fI : IntervalIntegrable (fun x => z*(f x)^2) volume 0 1 :=
      ((hf.pow 2).const_mul z).intervalIntegrable _ _
    have gI : IntervalIntegrable (fun x => (1/z)*(g x)^2) volume 0 1 :=
      ((hg.pow 2).const_mul (1/z)).intervalIntegrable _ _
    have ef (x : ℝ) : F x = (1/2)*(z*(f x)^2+(1/z)*(g x)^2) := by
      unfold F
      ring
    simp_rw [ef]
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add fI gI,intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
    unfold periodL2Sq
    ring
  rw [intervalIntegral.integral_neg,e] at L
  rw [e] at U
  exact abs_le.mpr ⟨L,U⟩

#print axioms periodL2Sq_three_sum
#print axioms abs_periodInner_young

end CenteredCubeSqrt
