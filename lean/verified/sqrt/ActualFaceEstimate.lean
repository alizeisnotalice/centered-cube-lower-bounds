import ActualCenteredFaceLaw
import TrueTiltIidSumLaw
import ActualIidFaceBound

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace CubeSqrtProbability

/-- Smooth replacement applied to the genuinely tilted window source,
with true per-coordinate centered facet law and its matching Gaussian. -/
theorem exists_true_tilt_winner_face_estimate {k : ℕ} (j : Fin k) :
    ∃ K : ℝ, 0 ≤ K ∧
    ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (f : Ω → ℝ) (hf : Integrable (fun w ↦ Real.exp (f w)) P)
      (G : Ω → Fin k → ℝ) (hG : Measurable G)
      (B : ℝ) (hB : 0 ≤ B)
      (hb : ∀ w i, |winnerFacetScore j (G w) i| ≤ B)
      (n : ℕ) (h r η : ℝ) (hη : 0 < η),
      let Q := P.tilted f
      let F (w : Ω) := winnerFacetScore j (G w)
      let m i := ∫ w, F w i ∂Q
      let A (w : Ω) (i : WinnerFacet j) := F w i - m i
      let μ := Q.map A
      let S := rawSecondMoment μ
      let ν := centeredGaussianCompanion S
      let z (i : WinnerFacet j) := n * m i
      (∀ i, n • (S i i).toNNReal ≠ 0) →
      |((Measure.pi fun _ : Fin n ↦ P).tilted (fun x ↦ ∑ i, f (x i))).real
        (faceEvent (fun x ↦ ∑ i, F (x i)) (winnerFacetStrict j)
          (winnerFacetThreshold j h r) 0) -
        (sumLaw ν n).real (faceEvent (fun x ↦ z+x) (winnerFacetStrict j)
          (winnerFacetThreshold j h r) 0)| ≤
      ((n:ℝ)*K/η^3) * ((2*B)^3 + stdGaussianThird*∑ i, (√(S i i).toNNReal)^3) +
           η * ∑ i, (√(2*Real.pi*((n • (S i i).toNNReal : ℝ≥0):ℝ)))⁻¹ := by
  classical
  obtain ⟨K,hK,hest⟩ := exists_actual_iid_bounded_face_estimate (ι := WinnerFacet j)
  refine ⟨K,hK,?_⟩
  intro Ω _ P _ f hf G hG B hB hb n h r η hη
  dsimp only
  intro hvar
  let Q := P.tilted f
  haveI : IsProbabilityMeasure Q := isProbabilityMeasure_tilted hf
  let F (w : Ω) := winnerFacetScore j (G w)
  have hF : Measurable F := (measurable_winnerFacetScore j).comp hG
  let m i := ∫ w, F w i ∂Q
  let A (w : Ω) (i : WinnerFacet j) := F w i - m i
  let μ := Q.map A
  let z (i : WinnerFacet j) := n * m i
  obtain ⟨hA,hμbound,hμmean⟩ := centered_facet_coordinate_law Q F hF B hB hb
  haveI : IsProbabilityMeasure μ := by dsimp [μ]; infer_instance
  let R := (Measure.pi fun _ : Fin n ↦ P).tilted (fun x ↦ ∑ i, f (x i))
  have hmap : R.map (fun x ↦ ∑ i, A (x i)) = sumLaw μ n :=
    true_product_tilt_score_sumLaw P f hf A hA n
  have hmapmeas : Measurable (fun x : Fin n → Ω ↦ ∑ i, A (x i)) :=
    Finset.measurable_sum _ (fun i _ ↦ hA.comp (measurable_pi_apply i))
  let E := faceEvent (fun x ↦ z+x) (winnerFacetStrict j) (winnerFacetThreshold j h r) 0
  have hE : MeasurableSet E :=
    measurableSet_faceEvent (fun x ↦ z+x) (fun i ↦ measurable_const.add (measurable_pi_apply i)) _ _ _
  have he : E =
      faceEvent (fun x ↦ z+x) (winnerFacetStrict j) (winnerFacetThreshold j h r) 0 := rfl
  have hs (x : Fin n → Ω) : z+(∑ i, A (x i)) = ∑ i, F (x i) := by
    funext b
    simp only [Pi.add_apply,Finset.sum_apply,A,Finset.sum_sub_distrib,
      Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,z]
    ring
  have hP : R.real (faceEvent (fun x ↦ ∑ i, F (x i)) (winnerFacetStrict j)
      (winnerFacetThreshold j h r) 0) = (sumLaw μ n).real E := by
    rw [← hmap,measureReal_def,measureReal_def,Measure.map_apply hmapmeas hE]
    suffices heq : faceEvent (fun x : Fin n → Ω ↦ ∑ i, F (x i)) (winnerFacetStrict j)
          (winnerFacetThreshold j h r) 0 = (fun x : Fin n → Ω ↦ ∑ i, A (x i)) ⁻¹' E by rw [heq]
    ext x
    change (∀ i, facePass _ ((∑ l, F (x l)) i) _) ↔
      (∀ i, facePass _ ((z+(∑ l, A (x l))) i) _)
    rw [hs]
  rw [hP]
  exact hest μ (2*B) (by positivity) hμbound hμmean n z _ _ η hη hvar

end CubeSqrtProbability
#print axioms CubeSqrtProbability.exists_true_tilt_winner_face_estimate
