import ConvolutionReplacement
import GaussianCompanion
import Mathlib.Probability.Independence.Basic

open MeasureTheory ProbabilityTheory
open scoped MeasureTheory NNReal BigOperators

namespace CubeSqrtProbability

theorem sumLaw_of_actual_iid {Ω E ι : Type*}
    [MeasurableSpace Ω] [MeasurableSpace E] [AddCommMonoid E] [MeasurableAdd₂ E]
    (P : Measure Ω) [IsProbabilityMeasure P] (μ : Measure E)
    (X : ι → Ω → E) (hI : iIndepFun X P) (hm : ∀ i, Measurable (X i))
    (hLaw : ∀ i, P.map (X i) = μ) (s : Finset ι) :
    P.map (fun w ↦ ∑ i ∈ s, X i w) = sumLaw μ s.card := by
  classical
  have hf (j : Finset ι) : (∑ i ∈ j, X i) = (fun w ↦ ∑ i ∈ j, X i w) := by
    funext w
    rw [Finset.sum_apply]
  have hl (j : Finset ι) : Measurable (∑ i ∈ j, X i) := by
    rw [hf]
    exact Finset.measurable_sum j (fun i _ ↦ hm i)
  induction s using Finset.induction_on with
  | empty =>
    simp [sumLaw,Measure.map_const]
  | insert i s hi ih =>
    have hsum : P.map (∑ j ∈ s, X j) = sumLaw μ s.card := by
      rw [hf]
      exact ih
    have hsumapp : (fun w ↦ ∑ j ∈ insert i s, X j w) = (∑ j ∈ s, X j) + X i := by
      funext w
      simp [Finset.sum_insert hi,Finset.sum_apply,add_comm]
    rw [hsumapp, (hI.indepFun_finsetSum_of_notMem hm hi).map_add_eq_map_conv_map (hl _) (hm i),
      hsum,hLaw i,Finset.card_insert_of_notMem hi]
    rfl

theorem sumLaw_centeredGaussian_marginal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Matrix ι ι ℝ) (hS : S.PosSemidef) (i : ι) (n : ℕ) :
    (sumLaw (centeredGaussianCompanion S) n).map (fun d ↦ d i) =
      gaussianReal 0 (n • (S i i).toNNReal) := by
  induction n with
  | zero =>
    simp [sumLaw,Measure.map_dirac' (measurable_pi_apply i),gaussianReal_zero_var]
  | succ n ih =>
    let L : (ι → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj i
    change (sumLaw (centeredGaussianCompanion S) n ∗ centeredGaussianCompanion S).map L =
      gaussianReal 0 ((n+1) • (S i i).toNNReal)
    rw [Measure.map_conv_continuousLinearMap]
    change (sumLaw (centeredGaussianCompanion S) n).map (fun d ↦ d i) ∗
      (centeredGaussianCompanion S).map (fun d ↦ d i) = _
    rw [ih, centeredGaussianCompanion_marginal S hS, gaussianReal_conv_gaussianReal,
      add_zero, succ_nsmul]

set_option maxHeartbeats 1500000 in
theorem sumLaw_shiftedGaussian_marginal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Matrix ι ι ℝ) (hS : S.PosSemidef) (i : ι) (n : ℕ) (a : ℝ) :
    (sumLaw (centeredGaussianCompanion S) n).map (fun d ↦ a+d i) =
      gaussianReal a (n • (S i i).toNNReal) := by
  have he : (fun d : ι → ℝ ↦ a+d i) = (fun x : ℝ ↦ a+x) ∘ (fun d : ι → ℝ ↦ d i) := rfl
  have hA : Measurable (fun x : ℝ ↦ a+x) := measurable_const.add measurable_id
  rw [he, ← Measure.map_map hA (measurable_pi_apply i),
    sumLaw_centeredGaussian_marginal S hS]
  simpa only [zero_add] using
     (gaussianReal_map_const_add (μ := 0) (v := n • (S i i).toNNReal) a)

end CubeSqrtProbability
#print axioms CubeSqrtProbability.sumLaw_of_actual_iid
#print axioms CubeSqrtProbability.sumLaw_shiftedGaussian_marginal
