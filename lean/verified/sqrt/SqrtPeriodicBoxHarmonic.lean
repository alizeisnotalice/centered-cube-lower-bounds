import SqrtActualWindowCentered

namespace CenteredCubeSqrt
open MeasureTheory Set
open scoped Interval

theorem cosine_integer_harmonic_periodic (m : ℕ) :
    Function.Periodic (fun x : ℝ => Real.cos (2*Real.pi*(m:ℝ)*x)) 1 := by
  intro x
  change Real.cos (2*Real.pi*(m:ℝ)*(x+1)) = Real.cos (2*Real.pi*(m:ℝ)*x)
  rw [show 2*Real.pi*(m:ℝ)*(x+1)=2*Real.pi*(m:ℝ)*x+(m:ℝ)*(2*Real.pi) by ring]
  exact Real.cos_add_nat_mul_two_pi _ _

/-- The exact real Fourier coefficient of one actual wrapped box. -/
theorem periodic_box_cosine_coefficient {δ : ℝ} (hδ0 : 0<δ) (hδ1 : δ<1)
    (a : ℝ) {m : ℕ} (hm : 0<m) :
    (∫ x in (0:ℝ)..1, periodicBoxDensity δ a x*Real.cos (2*Real.pi*(m:ℝ)*x)) =
      (Real.sin (Real.pi*(m:ℝ)*δ)/(Real.pi*(m:ℝ)*δ))*Real.cos (2*Real.pi*(m:ℝ)*a) := by
  let c := 2*Real.pi*(m:ℝ)
  let G (x : ℝ) := periodicBoxDensity δ a x*Real.cos (c*x)
  let H (x : ℝ) := (Icc (a-δ/2) (a+δ/2)).indicator (fun y => (1/δ)*Real.cos (c*y)) x
  have hc : 0<c := by
    have h : 0<(m:ℝ) := by exact_mod_cast hm
    dsimp [c]
    positivity
  have hP : Function.Periodic G 1 :=
    (periodicBoxDensity_periodic δ a).mul (cosine_integer_harmonic_periodic m)
  have hp := hP.intervalIntegral_add_eq 0 (a-1/2)
  rw [zero_add,show a-1/2+1=a+1/2 by ring] at hp
  have eq : EqOn G H (Ioo (a-1/2) (a+1/2)) := by
    intro x hx
    have eqRep : centeredPeriodRep (x-a)=x-a :=
      centeredPeriodRep_eq ⟨by linarith [hx.1],by linarith [hx.2]⟩
    have e : x-a∈Icc (-δ/2) (δ/2) ↔ x ∈ Icc (a-δ/2) (a+δ/2) := by
      simp only [mem_Icc]
      exact ⟨fun h => ⟨by linarith [h.1],by linarith [h.2]⟩,
        fun h => ⟨by linarith [h.1],by linarith [h.2]⟩⟩
    unfold G H periodicBoxDensity boxWindowDensity
    rw [eqRep]
    by_cases h : x∈Icc (a-δ/2) (a+δ/2)
    · rw [indicator_of_mem (e.mpr h),indicator_of_mem h]
    · rw [indicator_of_notMem (not_congr e |>.mpr h),indicator_of_notMem h,zero_mul]
  change (∫ x in (0:ℝ)..1,G x)=_
  rw [hp,intervalIntegral.integral_congr_Ioo_of_le (by linarith) eq]
  unfold H
  rw [intervalIntegral.integral_of_le (by linarith : a-1/2≤a+1/2),integral_indicator measurableSet_Icc]
  rw [Measure.restrict_restrict measurableSet_Icc]
  have eint : Icc (a-δ/2) (a+δ/2) ∩ Ioc (a-1/2) (a+1/2) = Icc (a-δ/2) (a+δ/2) := by
    refine inter_eq_left.mpr ?_
    intro y hy
    exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
  rw [eint,←setIntegral_congr_set Ioc_ae_eq_Icc,
    ←intervalIntegral.integral_of_le (by linarith : a-δ/2≤a+δ/2),
    intervalIntegral.integral_const_mul]
  have hi := intervalIntegral.integral_comp_mul_left (f:=Real.cos) (a:=a-δ/2) (b:=a+δ/2) hc.ne'
  rw [integral_cos] at hi
  rw [hi,show c*(a+δ/2)=c*a+c*δ/2 by ring,show c*(a-δ/2)=c*a-c*δ/2 by ring,
    Real.sin_add,Real.sin_sub,smul_eq_mul]
  have h : c*δ/2=Real.pi*(m:ℝ)*δ := by unfold c; ring
  rw [h]
  unfold c
  field_simp [Real.pi_ne_zero,hδ0.ne',show (m:ℝ)≠0 by exact_mod_cast hm.ne'] ; ring

#print axioms periodic_box_cosine_coefficient

end CenteredCubeSqrt
