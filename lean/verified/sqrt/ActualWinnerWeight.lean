import WinnerThreshold
import IsonormalWinnerLimitLaw
import WeightedWinnerComparison

open MeasureTheory ProbabilityTheory Set Filter CubeSqrtProbability
open scoped NNReal ENNReal Topology ProbabilityTheory
namespace CubeBrownian

lemma winnerFace_lintegral_le_one
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : Ω → ℝ) (D : Ω → E)
    (hmZ : Measurable Z) (hmD : Measurable D) (F : Set E) (hF : MeasurableSet F) :
    (∫⁻ w in {w | 0 < Z w ∧ D w ∈ F}, ENNReal.ofReal (Real.exp (-(Z w))) ∂μ) ≤ 1 := by
  let S := {w | 0 < Z w ∧ D w ∈ F}
  have h0 : MeasurableSet {w | 0 < Z w} := measurableSet_lt measurable_const hmZ
  have hS : MeasurableSet S := h0.inter (hmD hF)
  change (∫⁻ w in S, ENNReal.ofReal (Real.exp (-(Z w))) ∂μ) ≤ 1
  calc
    _ ≤ ∫⁻ w in S, (1 : ℝ≥0∞) ∂μ := setLIntegral_mono' hS (fun w hw ↦
      ENNReal.ofReal_le_one.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hw.1.le)))
    _ = μ S := by rw [lintegral_const,Measure.restrict_apply MeasurableSet.univ,univ_inter,one_mul]
    _ ≤ 1 := prob_le_one

/-- The actual source score's strict global exceedance is exactly the sum of
the same winner weights used by the Gaussian comparison and limit. -/
theorem finiteWinner_exceedance_eq_sum_faceWeight
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ} (hn : 0 < n)
    (X : Fin n → Ω → ℝ) (hm : ∀ i, Measurable (X i))
    (hInt : ∀ i, Integrable (fun w ↦ Real.exp (X i w)) μ)
    (hNorm : ∀ i, ∫ w, Real.exp (X i w) ∂μ = 1) (h : ℝ) :
    Real.exp h * μ.real {w | h < ⨆ i, X i w} =
      ∑ j, winnerFaceWeight (μ.tilted (X j)) (fun w ↦ X j w-h)
        (fun w i ↦ X i w-X j w) (winnerDifferenceFace j) := by
  let Q (j : Fin n) := μ.tilted (X j)
  let Z (j : Fin n) (w : Ω) := X j w-h
  let D (j : Fin n) (w : Ω) (i : Fin n) := X i w-X j w
  let F := winnerDifferenceFace (n:=n)
  let _ (j : Fin n) : IsProbabilityMeasure (Q j) := isProbabilityMeasure_tilted (hInt j)
  have hmZ (j : Fin n) : Measurable (Z j) := (hm j).sub_const _
  have hmD (j : Fin n) : Measurable (D j) := Measurable.of_eval fun i ↦ (hm i).sub (hm j)
  let M (j : Fin n) := ∫⁻ w in {w | 0 < Z j w ∧ D j w ∈ F j},
    ENNReal.ofReal (Real.exp (-(Z j w))) ∂(Q j)
  have hM (j : Fin n) : M j ≤ 1 :=
    winnerFace_lintegral_le_one (Q j) (Z j) (D j) (hmZ j) (hmD j) (F j)
      (measurableSet_winnerDifferenceFace j)
  have hEq (j : Fin n) : M j = ∫⁻ r : ℝ, expTailWeight r *
      (μ.tilted (X j)) (weightedWindow (X j) h r ∩ finiteWinner X j) := by
    have he := gaussian_face_layercake (Q j) (Z j) (D j) (hmZ j) (hmD j) (F j)
      (measurableSet_winnerDifferenceFace j)
    change M j = _ at he
    have hpre : D j ⁻¹' F j = finiteWinner X j := preimage_winnerDifferenceFace X j
    have hw (r : ℝ) : weightedWindow (Z j) 0 r = weightedWindow (X j) h r := by
      ext w
      change (0 < X j w-h ∧ X j w-h ≤ 0+r) ↔ (h < X j w ∧ X j w ≤ h+r)
      constructor <;> intro H <;> constructor <;> linarith only [H.1,H.2]
    simpa only [Q,hpre,hw] using he
  have H := finiteWinner_threshold_layercake μ hn X hm hInt hNorm h
  simp_rw [← hEq] at H
  have H' := congrArg ENNReal.toReal H
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos h).le,
    ENNReal.toReal_sum (fun j _ ↦ ne_top_of_le_ne_top ENNReal.one_ne_top (hM j))] at H'
  exact H'

end CubeBrownian
#print axioms CubeBrownian.finiteWinner_exceedance_eq_sum_faceWeight
