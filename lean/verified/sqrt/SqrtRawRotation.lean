import SqrtRawCellAverage

namespace CenteredCubeSqrt
open MeasureTheory Set
open scoped Interval
set_option maxHeartbeats 1800000

noncomputable def unitRotatedInner (f : ℝ→ℝ) (θ : ℝ) :=
  (∫ r in (0:ℝ)..1-θ, f r*f (r+θ))+(∫ r in 1-θ..(1:ℝ),f r*f (r+θ-1))

theorem unitRotatedInner_abs_le_energy {f : ℝ→ℝ} {θ A : ℝ}
    (hθ : θ∈Icc (0:ℝ) 1) (hm : Measurable f) (hA : ∀ r∈Icc (0:ℝ) 1,|f r|≤A) :
    |unitRotatedInner f θ| ≤ ∫ r in (0:ℝ)..1,(f r)^2 := by
  have hA0 : 0≤A := (abs_nonneg _).trans (hA 0 (by norm_num))
  have hi {a b s : ℝ} (hab : a≤b) (h1 : 0≤a) (h2 : b≤1) (h3 : 0≤a+s) (h4 : b+s≤1) :
      IntervalIntegrable (fun r => f r*f (r+s)) volume a b := by
    rw [intervalIntegrable_iff,uIoc_of_le hab]
    apply Measure.integrableOn_of_bounded (M:=A^2) (s_finite:=by simp [Real.volume_Ioc])
      (hm.mul (hm.comp (measurable_id.add measurable_const))).aestronglyMeasurable
    filter_upwards [ae_restrict_mem (μ:=volume) measurableSet_Ioc] with r hr
    change ‖f r * f (r+s)‖ ≤ A^2
    rw [Real.norm_eq_abs,abs_mul,pow_two]
    have hR : r∈Icc (0:ℝ) 1 := ⟨by linarith [hr.1],by linarith [hr.2]⟩
    have hS : r+s∈Icc (0:ℝ) 1 := ⟨by linarith [hr.1],by linarith [hr.2]⟩
    exact mul_le_mul (hA r hR) (hA (r+s) hS) (abs_nonneg _) hA0
  have hs {a b s : ℝ} (hab : a≤b) (h3 : 0≤a+s) (h4 : b+s≤1) :
      IntervalIntegrable (fun r => (f (r+s))^2) volume a b := by
    rw [intervalIntegrable_iff,uIoc_of_le hab]
    apply Measure.integrableOn_of_bounded (M:=A^2) (s_finite:=by simp [Real.volume_Ioc])
      ((hm.comp (measurable_id.add measurable_const)).pow_const 2).aestronglyMeasurable
    filter_upwards [ae_restrict_mem (μ:=volume) measurableSet_Ioc] with r hr
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _),←sq_abs]
    have hS : r+s∈Icc (0:ℝ) 1 := ⟨by linarith [hr.1],by linarith [hr.2]⟩
    exact pow_le_pow_left₀ (abs_nonneg _) (hA (r+s) hS) 2
  have hv {a b s : ℝ} (hab : a≤b) (h1 : 0≤a) (h2 : b≤1) (h3 : 0≤a+s) (h4 : b+s≤1) :
      |∫ r in a..b, f r*f (r+s)| ≤
        ((∫ r in a..b,(f r)^2)+(∫ r in a+s..b+s,(f r)^2))/2 := by
    have h4a := hs (s:=0) hab (by simpa using h1) (by simpa using h2)
    simp only [add_zero] at h4a
    have h4b := hs (s:=s) hab h3 h4
    refine (intervalIntegral.abs_integral_le_integral_abs hab).trans ?_
    have hp (r : ℝ) : |f r*f (r+s)| ≤ ((f r)^2+(f (r+s))^2)/2 := by
      rw [abs_mul]
      nlinarith [sq_nonneg (|f r|-|f (r+s)|),sq_abs (f r),sq_abs (f (r+s))]
    refine (intervalIntegral.integral_mono hab (hi hab h1 h2 h3 h4).abs
      ((h4a.add h4b).div_const 2) hp).trans_eq ?_
    rw [intervalIntegral.integral_div,intervalIntegral.integral_add h4a h4b,
      intervalIntegral.integral_comp_add_right (f:=fun x => (f x)^2) (a:=a) (b:=b) s]
  have l := hv (s:=θ) (a:=0) (b:=1-θ) (by linarith [hθ.2]) (by norm_num)
    (by linarith [hθ.1]) (by linarith [hθ.1]) (by linarith)
  have r := hv (s:=θ-1) (a:=1-θ) (b:=1) (by linarith [hθ.1])
    (by linarith [hθ.2]) (by norm_num) (by linarith) (by linarith [hθ.2])
  rw [zero_add,sub_add_cancel] at l
  rw [show 1-θ+(θ-1)=0 by ring,show 1+(θ-1)=θ by ring] at r
  unfold unitRotatedInner
  simp_rw [add_sub_assoc]
  refine (abs_add_le _ _).trans ((add_le_add l r).trans_eq ?_)
  have hsq (a b : ℝ) (hab : a≤b) (ha : 0≤a) (hb : b≤1) :
      IntervalIntegrable (fun r => (f r)^2) volume a b := by
    simpa only [add_zero] using hs (s:=0) hab (by simpa using ha) (by simpa using hb)
  have h₁ := intervalIntegral.integral_add_adjacent_intervals
    (hsq 0 (1-θ) (by linarith [hθ.2]) (by norm_num) (by linarith [hθ.1]))
    (hsq (1-θ) 1 (by linarith [hθ.1]) (by linarith [hθ.2]) (by norm_num))
  have h₂ := intervalIntegral.integral_add_adjacent_intervals
    (hsq 0 θ hθ.1 (by norm_num) hθ.2)
    (hsq θ 1 hθ.2 hθ.1 (by norm_num))
  linarith

#print axioms unitRotatedInner_abs_le_energy
end CenteredCubeSqrt
