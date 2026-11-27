import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace CenteredCubeSqrt
open MeasureTheory
open scoped Interval

theorem unit_phase_Taylor_remainder (x : ℝ) :
    ‖Complex.exp (Complex.I*(x:ℂ)) - 1 - Complex.I*(x:ℂ)‖ ≤ x^2/2 := by
  let F (y : ℝ) := Complex.exp (Complex.I*(y:ℂ))-1-Complex.I*(y:ℂ)
  let G (y : ℝ) := Complex.I*(Complex.exp (Complex.I*(y:ℂ))-1)
  have hc : Continuous G := by unfold G; fun_prop
  have hg (y : ℝ) : HasDerivAt F (G y) y := by
    have h1 : HasDerivAt (fun z : ℝ => Complex.I*(z:ℂ)) Complex.I y := by
      simpa only [Complex.ofRealCLM_apply,Complex.ofReal_one,mul_one] using (Complex.ofRealCLM.hasDerivAt (x:=y)).const_mul Complex.I
    have h2 := ((h1.cexp.sub_const 1).sub h1)
    convert h2 using 1
    unfold G
    ring
  have h0 : F 0 = 0 := by simp [F]
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=0) (b:=x)
    (fun y _ => hg y) (hc.intervalIntegrable _ _)
  rw [h0,sub_zero] at he
  have hbound (y : ℝ) : ‖G y‖≤|y| := by
    unfold G
    rw [norm_mul,Complex.norm_I,one_mul]
    exact Real.norm_exp_I_mul_ofReal_sub_one_le
  change ‖F x‖ ≤ x^2/2
  rw [←he]
  rcases le_total 0 x with hx | hx
  · refine (intervalIntegral.norm_integral_le_integral_norm hx).trans ?_
    have hI : IntervalIntegrable (fun y : ℝ => y) volume 0 x := continuous_id.intervalIntegrable _ _
    have hh := intervalIntegral.integral_mono_on hx (hc.norm.intervalIntegrable _ _) hI
      (fun y hy => (hbound y).trans_eq (abs_of_nonneg hy.1))
    refine hh.trans_eq ?_
    simp
  · rw [intervalIntegral.integral_symm x 0, norm_neg]
    refine (intervalIntegral.norm_integral_le_integral_norm hx).trans ?_
    have hI : IntervalIntegrable (fun y : ℝ => -y) volume x 0 := continuous_id.neg.intervalIntegrable _ _
    have hh := intervalIntegral.integral_mono_on hx (hc.norm.intervalIntegrable _ _) hI
      (fun y hy => (hbound y).trans_eq (abs_of_nonpos hy.2))
    refine hh.trans_eq ?_
    rw [intervalIntegral.integral_neg]
    simp; ring

#print axioms unit_phase_Taylor_remainder

end CenteredCubeSqrt
