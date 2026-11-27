import WalshEnergyHierarchy
import FarUniqueCorrection

namespace CenteredCubeSqrt
open MeasureTheory Set Classical Filter
open scoped Interval BigOperators
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem walshShift_cauchy {b : ℕ} (a c : NonzeroBinary b) {l r s : ℝ}
    (hlr : l≤r) (hl : 0≤l) (hr : r≤1) (hls : 0≤l+s) (hrs : r+s≤1) :
    |∫ t in l..r, walshCellPrimitive a t * walshCellPrimitive c (t+s)| ≤
      Real.sqrt (walshEnergy a) * Real.sqrt (walshEnergy c) := by
  let f := walshCellPrimitive a
  let g := fun t => walshCellPrimitive c (t+s)
  let μ := volume.restrict (Ioc l r)
  haveI : IsFiniteMeasure μ := Real.isFiniteMeasure_restrict_Ioc _ _
  have hf : MemLp f (ENNReal.ofReal (2:ℝ)) μ :=
    MemLp.of_bound (walshCellPrimitive_measurable a).aestronglyMeasurable 1
      (Eventually.of_forall fun t => by simpa using walshCellPrimitive_abs_le_one a t)
  have hg : MemLp g (ENNReal.ofReal (2:ℝ)) μ :=
    MemLp.of_bound ((walshCellPrimitive_measurable c).comp (measurable_id.add_const s)).aestronglyMeasurable
      1 (Eventually.of_forall fun t => by simpa using walshCellPrimitive_abs_le_one c (t+s))
  have hH := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two hf hg
  simp only [Real.norm_eq_abs, ← abs_mul,
      ← Nat.cast_ofNat (R:=ℝ) (n:=2), Real.rpow_natCast, sq_abs] at hH
  change (∫ t, |f t*g t| ∂μ) ≤
    (∫ t, (f t)^2 ∂μ) ^ (1/(2:ℝ)) * (∫ t, (g t)^2 ∂μ) ^ (1/(2:ℝ)) at hH
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hH
  refine (intervalIntegral.abs_integral_le_integral_abs hlr).trans ?_
  rw [intervalIntegral.integral_of_le hlr]
  refine hH.trans ?_
  have hFa := intervalIntegral.integral_mono_interval hl hlr hr
    (Eventually.of_forall fun t => sq_nonneg (f t)) (walshPrimitive_pow_intervalIntegrable a 0 1)
  have hGa := intervalIntegral.integral_mono_interval hls (add_le_add_left hlr s) hrs
    (Eventually.of_forall fun t => sq_nonneg (walshCellPrimitive c t)) (walshPrimitive_pow_intervalIntegrable c 0 1)
  have e : (∫ t in l..r, (g t)^2) = ∫ t in l+s..r+s, (walshCellPrimitive c t)^2 := by
    exact intervalIntegral.integral_comp_add_right (f:=fun t => (walshCellPrimitive c t)^2) s
  rw [←e,intervalIntegral.integral_of_le hlr] at hGa
  rw [intervalIntegral.integral_of_le hlr] at hFa
  exact mul_le_mul (Real.sqrt_le_sqrt hFa) (Real.sqrt_le_sqrt hGa) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

noncomputable def paperWalshQ (b : ℕ) :=
  Real.sqrt (upperWalshEnergy b * lowerWalshEnergy b)

theorem walshShift_distinct_le_Q {b : ℕ} (a c : NonzeroBinary (b+1)) (hac : a≠c)
    {l r s : ℝ} (hlr : l≤r) (hl : 0≤l) (hr : r≤1) (hls : 0≤l+s) (hrs : r+s≤1) :
    |∫ t in l..r, walshCellPrimitive a t * walshCellPrimitive c (t+s)| ≤ paperWalshQ (b+1) := by
  have eU : 0≤upperWalshEnergy (b+1) := by unfold upperWalshEnergy; positivity
  have eL : 0≤lowerWalshEnergy (b+1) := by unfold lowerWalshEnergy; positivity
  refine (walshShift_cauchy a c hlr hl hr hls hrs).trans ?_
  rcases walshEnergy_distinct a c hac with h | h
  · unfold paperWalshQ
    rw [mul_comm, Real.sqrt_mul eU]
    exact mul_le_mul (Real.sqrt_le_sqrt h.2) (Real.sqrt_le_sqrt h.1) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  · unfold paperWalshQ
    rw [Real.sqrt_mul eU]
    exact mul_le_mul (Real.sqrt_le_sqrt h.1) (Real.sqrt_le_sqrt h.2) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

#print axioms walshShift_distinct_le_Q
end CenteredCubeSqrt
