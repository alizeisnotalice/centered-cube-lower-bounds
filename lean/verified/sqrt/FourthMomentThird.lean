import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal ProbabilityTheory RealInnerProductSpace
namespace CubeSqrtPair

theorem centered_third_le_sd_fourth
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q] (V : Ω → ℝ) (hm : Measurable V)
    (h2 : MemLp V 2 Q) (m : ℝ) (hMean : ∫ w, V w ∂Q = m)
    (h4 : Integrable (fun w ↦ (V w-m)^4) Q) :
    Integrable (fun w ↦ |V w-m|^3) Q ∧
    (∫ w, |V w-m|^3 ∂Q) ≤ Real.sqrt (Var[V;Q]) * Real.sqrt (∫ w, (V w-m)^4 ∂Q) := by
  let a : Ω → ℝ := fun w ↦ |V w-m|
  let b : Ω → ℝ := fun w ↦ (V w-m)^2
  have ha : MemLp a 2 Q := (h2.sub (memLp_const m)).abs
  have hb : MemLp b 2 Q := by
    apply (memLp_two_iff_integrable_sq ((hm.sub_const m).pow_const 2).aestronglyMeasurable).mpr
    simpa only [← pow_mul] using h4
  let A := ha.toLp a
  let B := hb.toLp b
  have hA : (A : Ω → ℝ) =ᵐ[Q] a := MemLp.coeFn_toLp ha
  have hB : (B : Ω → ℝ) =ᵐ[Q] b := MemLp.coeFn_toLp hb
  have hAB : (fun w ↦ ⟪A w,B w⟫) =ᵐ[Q] (fun w ↦ |V w-m|^3) := by
    filter_upwards [hA,hB] with w hw hz
    rw [hw,hz]
    have hs : (V w-m)^2 = |V w-m|^2 := (sq_abs _).symm
    simp only [Real.inner_apply,a,b,hs]
    ring
  have hAA : (fun w ↦ ⟪A w,A w⟫) =ᵐ[Q] (fun w ↦ (V w-m)^2) := by
    filter_upwards [hA] with w hw
    rw [hw]
    simpa only [Real.inner_apply,a,pow_two] using sq_abs (V w-m)
  have hBB : (fun w ↦ ⟪B w,B w⟫) =ᵐ[Q] (fun w ↦ (V w-m)^4) := by
    filter_upwards [hB] with w hw
    rw [hw]
    simp only [Real.inner_apply,b]
    ring
  have hV : Var[V;Q] = ∫ w, (V w-m)^2 ∂Q := by rw [variance_eq_integral hm.aemeasurable,hMean]
  have haNorm : ‖A‖^2 = Var[V;Q] := by
    rw [← real_inner_self_eq_norm_sq,MeasureTheory.L2.inner_def,integral_congr_ae hAA,hV]
  have hbNorm : ‖B‖^2 = ∫ w, (V w-m)^4 ∂Q := by
    rw [← real_inner_self_eq_norm_sq,MeasureTheory.L2.inner_def,integral_congr_ae hBB]
  constructor
  · exact (MeasureTheory.L2.integrable_inner A B).congr hAB
  · rw [← integral_congr_ae hAB,← MeasureTheory.L2.inner_def,← haNorm,← hbNorm,
      Real.sqrt_sq (norm_nonneg _),Real.sqrt_sq (norm_nonneg _)]
    exact real_inner_le_norm _ _

end CubeSqrtPair
#print axioms CubeSqrtPair.centered_third_le_sd_fourth
