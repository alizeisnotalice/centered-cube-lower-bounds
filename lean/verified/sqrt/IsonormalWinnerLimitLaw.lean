import IsonormalTilt
import IsonormalScoreMoments
import GaussianWinner
import GaussianNullHyperplane

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology ProbabilityTheory
namespace CubeBrownian

def winnerDifferenceFace {n : ℕ} (j : Fin n) : Set (Fin n → ℝ) :=
  {z | ∀ i : Fin n, i ≠ j → if i < j then z i < 0 else z i ≤ 0}

theorem measurableSet_winnerDifferenceFace {n : ℕ} (j : Fin n) :
    MeasurableSet (winnerDifferenceFace j) := by
  have he : winnerDifferenceFace j =
      ⋂ i : Fin n, {z : Fin n → ℝ | i ≠ j → if i < j then z i < 0 else z i ≤ 0} := by
    ext z; simp [winnerDifferenceFace]
  rw [he]
  apply MeasurableSet.iInter
  intro i
  by_cases hij : i = j
  · simp [hij]
  · by_cases h : i < j
    · simpa [hij,h] using
        (measurableSet_lt (measurable_pi_apply i) measurable_const :
          MeasurableSet {z : Fin n → ℝ | z i < (0:ℝ)})
    · simpa [hij,h] using
        (measurableSet_le (measurable_pi_apply i) measurable_const :
          MeasurableSet {z : Fin n → ℝ | z i ≤ (0:ℝ)})

theorem preimage_winnerDifferenceFace {Ω : Type*} {n : ℕ} (X : Fin n → Ω → ℝ)
    (j : Fin n) :
    (fun w i ↦ X i w-X j w) ⁻¹' winnerDifferenceFace j = finiteWinner X j := by
  ext w
  change (∀ i : Fin n, i ≠ j → if i < j then X i w-X j w < 0 else X i w-X j w ≤ 0) ↔
    (∀ i, X i w ≤ X j w) ∧ ∀ i < j, X i w < X j w
  constructor
  · intro h
    constructor
    · intro i
      rcases eq_or_ne i j with rfl|hij
      · exact le_rfl
      · by_cases hi : i < j
        · exact (sub_neg.mp (by simpa only [hi,ite_true] using h i hij)).le
        · exact sub_nonpos.mp (by simpa only [hi,ite_false] using h i hij)
    · intro i hi
      exact sub_neg.mp (by simpa only [hi,ite_true] using h i (ne_of_lt hi))
  · intro h i hi
    by_cases hij : i < j
    · simpa only [hij,ite_true] using sub_neg.mpr (h.2 i hij)
    · simpa only [hij,ite_false] using sub_nonpos.mpr (h.1 i)

/-- The exact limiting face masses sum to the centered Gaussian mesh maximum
expectation; no equality/normalization is assumed. -/
theorem isonormal_winner_face_sum_expMax
    {Ω H : Type*} [MeasurableSpace Ω] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : H →ₗ[ℝ] (Ω → ℝ)) (hmW : ∀ x, Measurable (W x))
    (hW : ∀ x, HasLaw (W x) (gaussianReal 0 (isoVar 1 x)) μ)
    (k : ℝ≥0) {n : ℕ} (hn : 0 < n) (f : Fin n → H) :
    (∑ j, (μ.map (fun w i ↦ isoScore W k (f i-f j) w)) (winnerDifferenceFace j)) =
      ∫⁻ w, ENNReal.ofReal (Real.exp (⨆ i, isoScore W k (f i) w)) ∂μ := by
  let X (i : Fin n) := isoScore W k (f i)
  have hm (i : Fin n) : Measurable (X i) :=
    (measurable_const.mul (hmW (f i))).sub_const _
  have hEq (j : Fin n) : (μ.map (fun w i ↦ isoScore W k (f i-f j) w))
      (winnerDifferenceFace j) = (μ.tilted (X j)) (finiteWinner X j) := by
    have hM : Measurable (fun w i ↦ X i w-X j w) :=
      Measurable.of_eval (fun i ↦ (hm i).sub (hm j))
    rw [← isoScore_tilt_difference_law μ W hmW hW k f j,
      Measure.map_apply hM (measurableSet_winnerDifferenceFace j),preimage_winnerDifferenceFace]
  simp_rw [hEq]
  exact finiteWinner_gaussian_tilted_sum μ hn X hm (fun i ↦ isoVar k (f i))
    (fun i ↦ isoScore_hasLaw μ W hW k (f i))

end CubeBrownian
#print axioms CubeBrownian.isonormal_winner_face_sum_expMax
