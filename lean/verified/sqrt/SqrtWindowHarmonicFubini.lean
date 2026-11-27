import SqrtWindowHarmonicShift
import Mathlib.MeasureTheory.Integral.Prod

namespace CenteredCubeSqrt
open MeasureTheory Set
open scoped Interval

/-- Move the actual box integration outside the window’s harmonic moment.
This is a compact rectangle integral of a bounded measurable function. -/
theorem box_window_fubini {δ a l u c : ℝ} (hδ : 0<δ) (hlu : l≤u) :
    (∫ x in (0:ℝ)..1, (∫ t in l..u, periodicBoxDensity δ a (x+t))*Real.cos (c*x)) =
      ∫ t in l..u, ∫ x in (0:ℝ)..1, periodicBoxDensity δ a (x+t)*Real.cos (c*x) := by
  let X : Measure ℝ := volume.restrict (Ioc 0 1)
  let Y : Measure ℝ := volume.restrict (Ioc l u)
  let f (x t : ℝ) := periodicBoxDensity δ a (x+t)*Real.cos (c*x)
  have h₁ : IsFiniteMeasure X := ⟨by unfold X; rw [Measure.restrict_apply_univ]; simp [Real.volume_Ioc]⟩
  have h₂ : IsFiniteMeasure Y := ⟨by unfold Y; rw [Measure.restrict_apply_univ]; simp [Real.volume_Ioc]⟩
  let : IsFiniteMeasure X := h₁
  let : IsFiniteMeasure Y := h₂
  have hmeas : Measurable (Function.uncurry f) :=
    ((periodicBoxDensity_measurable δ a).comp (measurable_fst.add measurable_snd)).mul
      (Real.continuous_cos.measurable.comp (measurable_const.mul measurable_fst))
  have I : Integrable (Function.uncurry f) (X.prod Y) := by
    apply (integrableOn_univ.mp ?_)
    apply Measure.integrableOn_of_bounded (M:=1/δ) (s_finite:=(measure_lt_top (X.prod Y) Set.univ).ne)
      hmeas.aestronglyMeasurable
    apply Filter.Eventually.of_forall
    rintro ⟨x,t⟩
    change ‖periodicBoxDensity δ a (x+t)*Real.cos (c*x)‖ ≤ 1/δ
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (periodicBoxDensity_bounds hδ a (x+t)).1]
    exact (mul_le_of_le_one_right (periodicBoxDensity_bounds hδ a (x+t)).1
      (Real.abs_cos_le_one _)).trans (periodicBoxDensity_bounds hδ a (x+t)).2
  simp_rw [intervalIntegral.integral_of_le hlu,intervalIntegral.integral_of_le (show (0:ℝ)≤1 by norm_num)]
  have hterm (x : ℝ) : (∫ t, periodicBoxDensity δ a (x+t) ∂Y)*Real.cos (c*x) =
      ∫ t, f x t ∂Y := by
    rw [integral_mul_const]
  change (∫ x, (∫ t, periodicBoxDensity δ a (x+t) ∂Y)*Real.cos (c*x) ∂X) =
    ∫ t, ∫ x, f x t ∂X ∂Y
  simp_rw [hterm]
  exact integral_integral_swap I

theorem actual_single_box_window_cosine {δ a L : ℝ} (hδ0 : 0<δ) (hδ1 : δ<1)
    (hL : 0≤L) {m : ℕ} (hm : 0<m) :
    let c := 2*Real.pi*(m:ℝ)
    (∫ x in (0:ℝ)..1, (∫ y in x-L/2..x+L/2, periodicBoxDensity δ a y)*Real.cos (c*x)) =
      (Real.sin (Real.pi*(m:ℝ)*L)/(Real.pi*(m:ℝ))) *
      (Real.sin (Real.pi*(m:ℝ)*δ)/(Real.pi*(m:ℝ)*δ)) *
      Real.cos (2*Real.pi*(m:ℝ)*a) := by
  let c := 2*Real.pi*(m:ℝ)
  let G := ∫ y in (0:ℝ)..1, periodicBoxDensity δ a y*Real.cos (c*y)
  let H := ∫ y in (0:ℝ)..1, periodicBoxDensity δ a y*Real.sin (c*y)
  have hc : 0<c := by
    have h : 0<(m:ℝ) := by exact_mod_cast hm
    dsimp [c]
    positivity
  have e (x : ℝ) : (∫ y in x-L/2..x+L/2, periodicBoxDensity δ a y) =
    ∫ t in -L/2..L/2, periodicBoxDensity δ a (x+t) := by
    rw [intervalIntegral.integral_comp_add_left]
    congr 1
    ring
  change (∫ x in (0:ℝ)..1, (∫ y in x-L/2..x+L/2, periodicBoxDensity δ a y)*Real.cos (c*x)) = _
  simp_rw [e]
  rw [box_window_fubini hδ0 (by linarith : -L/2≤L/2)]
  have hshift (t : ℝ) :
      (∫ x in (0:ℝ)..1, periodicBoxDensity δ a (x+t)*Real.cos (c*x)) =
        Real.cos (c*t)*G+Real.sin (c*t)*H := box_harmonic_shift hδ0 a t m
  simp_rw [hshift]
  have hG : Continuous (fun y => Real.cos (c*y)*G) :=
    (Real.continuous_cos.comp (continuous_const.mul continuous_id)).mul continuous_const
  have hH : Continuous (fun y => Real.sin (c*y)*H) :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).mul continuous_const
  change (∫ t in -L/2..L/2, Real.cos (c*t)*G+Real.sin (c*t)*H) = _
  rw [intervalIntegral.integral_add (hG.intervalIntegrable _ _) (hH.intervalIntegrable _ _),
    intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const]
  have hcos := intervalIntegral.integral_comp_mul_left (f:=Real.cos) (a:=-L/2) (b:=L/2) hc.ne'
  have hsin := intervalIntegral.integral_comp_mul_left (f:=Real.sin) (a:=-L/2) (b:=L/2) hc.ne'
  rw [integral_cos,show c*(-L/2)= -(c*(L/2)) by ring,Real.sin_neg,
    sub_neg_eq_add,smul_eq_mul] at hcos
  rw [integral_sin,show c*(-L/2)= -(c*(L/2)) by ring,Real.cos_neg,sub_self,smul_zero] at hsin
  rw [hcos,hsin,zero_mul,add_zero]
  have e' : c*(L/2)=Real.pi*(m:ℝ)*L := by dsimp [c]; ring
  have hv : c⁻¹*(Real.sin (c*(L/2))+Real.sin (c*(L/2))) =
      Real.sin (Real.pi*(m:ℝ)*L)/(Real.pi*(m:ℝ)) := by
    rw [e']
    dsimp [c]
    have hM : (m:ℝ)≠0 := by exact_mod_cast hm.ne'
    field_simp [hM,Real.pi_ne_zero]
    ring
  rw [hv]
  dsimp only [G]
  rw [periodic_box_cosine_coefficient hδ0 hδ1 a hm]
  ring

#print axioms box_window_fubini
#print axioms actual_single_box_window_cosine

end CenteredCubeSqrt
