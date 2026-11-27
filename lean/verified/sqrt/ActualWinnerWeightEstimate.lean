import ActualGaussianFacetSign
import ActualFaceEstimate
import FaceWeightedTransfer

open MeasureTheory ProbabilityTheory Filter CubeBrownian
open scoped BigOperators NNReal
namespace CubeSqrtProbability

/-- Genuine one-anchor Esscher product winner weight is close to its
canonical (possibly singular) Gaussian winner weight with the same explicit
rate as the uniform facet estimate. -/
theorem exists_true_tilt_winner_weight_estimate {k : ℕ} (j : Fin k) :
    ∃ K : ℝ, 0 ≤ K ∧
    ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (f : Ω → ℝ) (hf : Integrable (fun w ↦ Real.exp (f w)) P)
      (G : Ω → Fin k → ℝ) (hG : Measurable G)
      (B : ℝ) (hB : 0 ≤ B)
      (hb : ∀ w i, |winnerFacetScore j (G w) i| ≤ B)
      (n : ℕ) (h η : ℝ) (hη : 0 < η),
      let Q := P.tilted f
      let F (w : Ω) := winnerFacetScore j (G w)
      let m i := ∫ w, F w i ∂Q
      let A (w : Ω) (i : WinnerFacet j) := F w i - m i
      let μ := Q.map A
      let S := rawSecondMoment μ
      let ν := centeredGaussianCompanion S
      let z (i : WinnerFacet j) := n * m i
      let R := (Measure.pi fun _ : Fin n ↦ P).tilted (fun x ↦ ∑ i, f (x i))
      let X (x : Fin n → Ω) := ∑ i, F (x i)
      let X' (x : WinnerFacet j → ℝ) := z+x
      (∀ i, n • (S i i).toNNReal ≠ 0) →
      |winnerFaceWeight R (fun x ↦ X x (.inl true)-h) (facetRelative j ∘ X)
          (facetWinnerRegion j) -
       winnerFaceWeight (sumLaw ν n) (fun x ↦ X' x (.inl true)-h) (facetRelative j ∘ X')
          (facetWinnerRegion j)| ≤
      ((n:ℝ)*K/η^3) * ((2*B)^3 + stdGaussianThird*∑ i, (√(S i i).toNNReal)^3) +
           η * ∑ i, (√(2*Real.pi*((n • (S i i).toNNReal : ℝ≥0):ℝ)))⁻¹ := by
  classical
  obtain ⟨K,hK,hest⟩ := exists_true_tilt_winner_face_estimate j
  refine ⟨K,hK,?_⟩
  intro Ω _ P _ f hf G hG B hB hb n h η hη
  dsimp only
  intro hvar
  let Q := P.tilted f
  haveI : IsProbabilityMeasure Q := isProbabilityMeasure_tilted hf
  let F (w : Ω) := winnerFacetScore j (G w)
  have mF : Measurable F := (measurable_winnerFacetScore j).comp hG
  let m i := ∫ w, F w i ∂Q
  let A (w : Ω) (i : WinnerFacet j) := F w i - m i
  let μ := Q.map A
  let S := rawSecondMoment μ
  let ν := centeredGaussianCompanion S
  let z (i : WinnerFacet j) := n * m i
  let R := (Measure.pi fun _ : Fin n ↦ P).tilted (fun x ↦ ∑ i, f (x i))
  let X (x : Fin n → Ω) := ∑ i, F (x i)
  let X' (x : WinnerFacet j → ℝ) := z+x
  haveI : IsProbabilityMeasure R := by
    dsimp [R]
    rw [true_product_tilt_eq_general P f hf]
    infer_instance
  haveI : IsProbabilityMeasure μ := by dsimp [μ]; infer_instance
  have hX : Measurable X := Finset.measurable_sum _ (fun i _ ↦ mF.comp (measurable_pi_apply i))
  have hX' : Measurable X' := measurable_const.add measurable_id
  have hsign : ∀ᵐ w ∂R, X w (.inl false) = -X w (.inl true) :=
    Eventually.of_forall fun w ↦ by
      simp only [X,Finset.sum_apply,F,winnerFacetScore,Finset.sum_neg_distrib]
  obtain ⟨_,hμbound,_⟩ := centered_facet_coordinate_law Q F mF B hB hb
  obtain ⟨hμI,_⟩ := integrable_third_norm_of_bound μ (2*B) (by positivity) hμbound
  have hMuI (i t : WinnerFacet j) : Integrable (fun d : WinnerFacet j → ℝ ↦ d i*d t) μ := by
    let p : Fin 2 → WinnerFacet j := ![i,t]
    simpa [Fin.prod_univ_two,p] using integrable_coordinate_monomial_of_third_norm μ hμI
      (show (2:ℕ) ≤ 3 by decide) p
  have hS : S.PosSemidef := posSemidef_rawSecondMoment μ hMuI
  have hsign' : ∀ᵐ w ∂sumLaw ν n, X' w (.inl false) = -X' w (.inl true) :=
    true_winner_gaussian_facet_sign Q j G hG n hS
  exact weighted_error_of_facet_error R (sumLaw ν n) j h X X' hX hX' hsign hsign' _
    (fun r _ ↦ hest P f hf G hG B hB hb n h r η hη hvar)

end CubeSqrtProbability
#print axioms CubeSqrtProbability.exists_true_tilt_winner_weight_estimate
