import SqrtActualBaselineIncrement

namespace CenteredCubeSqrt
open MeasureTheory
open scoped Interval BigOperators

theorem periodicBoxDensity_periodic (delta a : ℝ) :
    Function.Periodic (periodicBoxDensity delta a) 1 := by
  intro x
  unfold periodicBoxDensity
  rw [show x+1-a=(x-a)+(1:ℤ) by norm_num; ring, centeredPeriodRep_int]

theorem atomBoxSum_periodic {B K : ℕ} [NeZero K] (f : ZMod K → Fin B) (delta : ℝ) :
    Function.Periodic (atomBoxSum f delta) 1 := by
  intro x
  unfold atomBoxSum
  exact Finset.sum_congr rfl fun j _ => periodicBoxDensity_periodic delta (paperAtomCenter f j) x

theorem atomBoxSum_period_integral {B K : ℕ} [NeZero K] (f : ZMod K → Fin B)
    (hB : 0<B) (hk : 2≤K) {delta : ℝ} (hδ0 : 0<delta) (hδ : delta<1/((B:ℝ)*K)) :
    (∫ x in (0:ℝ)..1, atomBoxSum f delta x) = (K:ℝ) := by
  have h := atomBoxSum_grid_primitive hB hk f hδ0 hδ (K:ℤ)
  have hK : (K:ℝ) ≠ 0 := by exact_mod_cast (show K ≠ 0 by omega)
  push_cast at h
  rwa [div_self hK] at h

theorem actualAtomicPrimitive_periodic {B K : ℕ} [NeZero K] (f : ZMod K → Fin B)
    (hB : 0<B) (hk : 2≤K) {delta : ℝ} (hδ0 : 0<delta) (hδ : delta<1/((B:ℝ)*K)) :
    Function.Periodic (actualAtomicPrimitive f delta) 1 := by
  intro x
  have h := (atomBoxSum_periodic f delta).intervalIntegral_add_eq_add 0 x
    (fun a b => atomBoxSum_intervalIntegrable f hδ0 a b)
  rw [zero_add,atomBoxSum_period_integral f hB hk hδ0 hδ] at h
  unfold actualAtomicPrimitive
  rw [h]
  ring

theorem actualAtomicWindow_integral_zero {B K : ℕ} [NeZero K] (f : ZMod K → Fin B)
    (hB : 0<B) (hk : 2≤K) {delta : ℝ} (hδ0 : 0<delta) (hδ : delta<1/((B:ℝ)*K))
    (L : ℝ) :
    (∫ x in (0:ℝ)..1, actualAtomicWindow f delta L x) = 0 := by
  let F := actualAtomicPrimitive f delta
  have I : ∀ a b, IntervalIntegrable (atomBoxSum f delta) volume a b :=
    fun a b => atomBoxSum_intervalIntegrable f hδ0 a b
  have hF : Continuous F :=
    (intervalIntegral.continuous_primitive I 0).sub (continuous_const.mul continuous_id)
  have he : actualAtomicWindow f delta L = fun x => F (x+L/2)-F (x+ -(L/2)) := by
    funext x
    simpa only [sub_eq_add_neg] using actualAtomicWindow_eq_primitive f (L:=L) hδ0 x
  change (∫ x in (0:ℝ)..1, actualAtomicWindow f delta L x) = 0
  have i1 : IntervalIntegrable (fun x => F (x+L/2)) volume 0 1 :=
    (hF.comp (continuous_id.add continuous_const)).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun x => F (x+ -(L/2))) volume 0 1 :=
    (hF.comp (continuous_id.add continuous_const)).intervalIntegrable _ _
  rw [he,intervalIntegral.integral_sub i1 i2,
    intervalIntegral.integral_comp_add_right,intervalIntegral.integral_comp_add_right]
  simpa only [zero_add, add_comm (1:ℝ), sub_eq_zero] using
    (actualAtomicPrimitive_periodic f hB hk hδ0 hδ).intervalIntegral_add_eq (L/2) (-(L/2))

theorem integral_cos_n_period (m : ℕ) :
    (∫ x in (0:ℝ)..1, Real.cos (((m:ℝ)+1)*(2*Real.pi)*x)) = 0 := by
  let c : ℝ := ((m:ℝ)+1)*(2*Real.pi)
  have hc : 0<c := by dsimp [c]; positivity
  have h := intervalIntegral.integral_comp_mul_left (f:=Real.cos) (a:=0) (b:=1) hc.ne'
  rw [mul_zero,mul_one,integral_cos,Real.sin_zero,sub_zero] at h
  change (∫ x in (0:ℝ)..1, Real.cos (c*x)) = 0
  rw [h]
  have e : c = (((m+1)*2:ℕ):ℝ)*Real.pi := by dsimp [c]; push_cast; ring
  rw [e,Real.sin_nat_mul_pi,smul_zero]

theorem actualLowSpectrum_integral_zero (M : ℕ) (L : ℝ) :
    (∫ x in (0:ℝ)..1, actualLowSpectrum M L x) = 0 := by
  unfold actualLowSpectrum
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_eq_zero
    intro m _
    rw [intervalIntegral.integral_const_mul,integral_cos_n_period,mul_zero]
  · intro m _
    have h : Continuous (fun x : ℝ => lowSpectrumAmp m * Real.sin (((m:ℝ)+1)*Real.pi*L) *
      Real.cos (((m:ℝ)+1)*(2*Real.pi)*x)) := by fun_prop
    exact h.intervalIntegrable _ _

theorem actualWindowPerturbation_integral_zero {B K : ℕ} [NeZero K]
    (f : ZMod K → Fin B) (M : ℕ) (p : ℝ) (hB : 0<B) (hk : 2≤K)
    {delta L : ℝ} (hδ0 : 0<delta) (hδ : delta<1/((B:ℝ)*K)) (hL : 0<L) :
    (∫ x in (0:ℝ)..1, actualWindowPerturbation f M p delta L x) = 0 := by
  simp_rw [actualWindowPerturbation_formula f M p hδ0 hL]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add ((actualAtomicWindow_continuous f hδ0 L).intervalIntegrable _ _)
      ((actualLowSpectrum_continuous M L).intervalIntegrable _ _),
    actualAtomicWindow_integral_zero f hB hk hδ0 hδ,actualLowSpectrum_integral_zero,
    zero_add,mul_zero]

#print axioms actualAtomicPrimitive_periodic
#print axioms actualWindowPerturbation_integral_zero

end CenteredCubeSqrt
