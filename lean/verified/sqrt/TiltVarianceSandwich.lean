import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology ProbabilityTheory
namespace CubeSqrtPair

theorem sq_shift_integral_eq_variance
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : MemLp X 2 μ) (c : ℝ) :
    (∫ x, (X x-c)^2 ∂μ) = Var[X; μ]+((∫ x, X x ∂μ)-c)^2 := by
  have hW : MemLp (fun w ↦ X w-c) 2 μ := hX.sub (memLp_const c)
  have h := variance_eq_sub hW
  rw [variance_sub_const hX.aestronglyMeasurable,
    integral_sub (hX.integrable one_le_two) (integrable_const _)] at h
  simp only [integral_const,probReal_univ,smul_eq_mul,one_mul] at h
  change Var[X;μ] = (∫ x, (X x-c)^2 ∂μ)-((∫ x, X x ∂μ)-c)^2 at h
  linarith only [h]

/-- Uniform density bounds give exact comparison of variances via the
variational identity for variance. This loses no extra smallness factors. -/
theorem tilted_variance_sandwich
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (V X : Ω → ℝ)
    (hm : Measurable V) (hInt : Integrable (fun w ↦ Real.exp (V w)) P)
    (hP : MemLp X 2 P) (hQ : MemLp X 2 (P.tilted V))
    (a b : ℝ) (ha : 0 ≤ a)
    (hD : ∀ w, a ≤ Real.exp (V w)/(∫ z, Real.exp (V z) ∂P) ∧
      Real.exp (V w)/(∫ z, Real.exp (V z) ∂P) ≤ b) :
    a*Var[X;P] ≤ Var[X;P.tilted V] ∧ Var[X;P.tilted V] ≤ b*Var[X;P] := by
  let Q := P.tilted V
  let D := fun w ↦ Real.exp (V w)/(∫ z, Real.exp (V z) ∂P)
  let _ : IsProbabilityMeasure Q := isProbabilityMeasure_tilted hInt
  have hDm : Measurable D := (Real.measurable_exp.comp hm).div_const _
  have hD₀ (w : Ω) : 0 ≤ D w := ha.trans (hD w).1
  have hSq (c : ℝ) : a*(∫ x, (X x-c)^2 ∂P) ≤ (∫ x, (X x-c)^2 ∂Q) ∧
      (∫ x, (X x-c)^2 ∂Q) ≤ b*(∫ x, (X x-c)^2 ∂P) := by
    have h2 : MemLp (fun x ↦ X x-c) 2 P := hP.sub (memLp_const c)
    have hI := (memLp_two_iff_integrable_sq h2.aestronglyMeasurable).1 h2
    have hMa : Integrable (fun w ↦ a*(X w-c)^2) P := hI.const_mul _
    have hMb : Integrable (fun w ↦ b*(X w-c)^2) P := hI.const_mul _
    have hLo (w : Ω) : a*(X w-c)^2 ≤ D w*(X w-c)^2 :=
      mul_le_mul_of_nonneg_right (hD w).1 (sq_nonneg _)
    have hHi (w : Ω) : D w*(X w-c)^2 ≤ b*(X w-c)^2 :=
      mul_le_mul_of_nonneg_right (hD w).2 (sq_nonneg _)
    have hDX : Integrable (fun w ↦ D w*(X w-c)^2) P := by
      apply hMb.mono' (hDm.aestronglyMeasurable.mul hI.aestronglyMeasurable)
      exact Eventually.of_forall fun w ↦ by
        change ‖D w*(X w-c)^2‖ ≤ b*(X w-c)^2
        rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (hD₀ w) (sq_nonneg _))]
        exact hHi w
    have hA := integral_mono_ae hMa hDX (Eventually.of_forall hLo)
    have hB := integral_mono_ae hDX hMb (Eventually.of_forall hHi)
    rw [integral_const_mul] at hA hB
    change a*(∫ x, (X x-c)^2 ∂P) ≤ (∫ x, (X x-c)^2 ∂(P.tilted V)) ∧ _
    have hEq : ∫ x, (X x-c)^2 ∂(P.tilted V) = ∫ w, D w*(X w-c)^2 ∂P := by
      simpa only [D,smul_eq_mul] using
        (integral_tilted (μ:=P) V (fun x ↦ (X x-c)^2))
    rw [hEq]
    exact ⟨hA,hB⟩
  have hPvar (c : ℝ) := sq_shift_integral_eq_variance P X hP c
  have hQvar (c : ℝ) := sq_shift_integral_eq_variance Q X hQ c
  have hLo := (hSq (∫ x, X x ∂Q)).1
  rw [hPvar,hQvar,sub_self,zero_pow (by norm_num : (2:ℕ)≠0),add_zero] at hLo
  have hHi := (hSq (∫ x, X x ∂P)).2
  rw [hPvar,hQvar,sub_self,zero_pow (by norm_num : (2:ℕ)≠0),add_zero] at hHi
  exact ⟨le_trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (sq_nonneg _)) ha) hLo,
    le_trans (le_add_of_nonneg_right (sq_nonneg _)) hHi⟩

end CubeSqrtPair
#print axioms CubeSqrtPair.tilted_variance_sandwich
