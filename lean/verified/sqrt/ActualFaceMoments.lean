import ActualCenteredFaceLaw
import GaussianCompanion

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators
namespace CubeSqrtProbability

/-- The centered facet law's raw Gram entry is the centered covariance of
the actual tilted-source coordinates, not a stipulated covariance. -/
theorem centered_facet_raw_matrix_covariance
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (Q : Measure Ω) (G : Ω → ι → ℝ) (hG : Measurable G) (i j : ι) :
    let m (i : ι) := ∫ w, G w i ∂Q
    let A (w : Ω) (i : ι) := G w i - m i
    rawSecondMoment (Q.map A) i j = covariance (fun w ↦ G w i) (fun w ↦ G w j) Q := by
  dsimp only
  let m (i : ι) := ∫ w, G w i ∂Q
  let A (w : Ω) (i : ι) := G w i - m i
  have hmA : Measurable A :=
    Measurable.of_eval fun i ↦ ((measurable_pi_apply i).comp hG).sub measurable_const
  unfold rawSecondMoment covariance
  exact integral_map (μ := Q) (φ := A) hmA.aemeasurable
    (f := fun d : ι → ℝ ↦ d i*d j) ((measurable_pi_apply i).mul
      (measurable_pi_apply j)).aestronglyMeasurable

theorem winnerFacetScore_sum {k : ℕ} (j : Fin k) {ι : Type*} (s : Finset ι)
    (G : ι → Fin k → ℝ) :
    winnerFacetScore j (∑ i ∈ s, G i) = ∑ i ∈ s, winnerFacetScore j (G i) := by
  funext b
  rcases b with b | b
  · cases b <;> simp [winnerFacetScore,Finset.sum_apply,Finset.sum_neg_distrib]
  · simp [winnerFacetScore,Finset.sum_apply,Finset.sum_sub_distrib]

/-- Uniform tiny-coordinate amplitude gives the midpoint and relative facet
bounds for the actual log scores used in the manuscript. -/
theorem log_perturbation_winnerFacetScore_bound {Ω : Type*} {k : ℕ}
    (j : Fin k) (d : Fin k → Ω → ℝ)
    {a : ℝ} (ha : a ≤ 1/2) (hd : ∀ i w, |d i w| ≤ a) (w : Ω) (b : WinnerFacet j) :
    |winnerFacetScore j (fun i ↦ Real.log (1+d i w)) b| ≤ 4*a := by
  have h (i : Fin k) : |Real.log (1+d i w)| ≤ 2*a :=
    (log1p_abs_le ha (hd i w)).trans (by linarith [hd i w])
  have ha0 := (abs_nonneg _).trans (hd j w)
  rcases b with b | b
  · cases b <;> simp [winnerFacetScore] <;> linarith [h j]
  · apply (abs_sub _ _).trans
    simp only [winnerFacetScore]
    linarith [h b.val,h j]

end CubeSqrtProbability
#print axioms CubeSqrtProbability.centered_facet_raw_matrix_covariance
#print axioms CubeSqrtProbability.winnerFacetScore_sum
#print axioms CubeSqrtProbability.log_perturbation_winnerFacetScore_bound
