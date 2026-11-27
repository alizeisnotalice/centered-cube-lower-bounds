import ActualFaceMoments
import WeightedWinnerComparison

open MeasureTheory ProbabilityTheory Filter Set CubeBrownian
namespace CubeSqrtProbability

def facetWinnerRegion {k : ℕ} (j : Fin k) : Set (Fin k → ℝ) :=
  {z | ∀ i : Fin k, i ≠ j → if i < j then z i < 0 else z i ≤ 0}

noncomputable def facetRelative {k : ℕ} (j : Fin k) (z : WinnerFacet j → ℝ) :
    Fin k → ℝ :=
  fun i ↦ if hi : i ≠ j then z (.inr ⟨i,hi⟩) else 0

theorem measurable_facetRelative {k : ℕ} (j : Fin k) : Measurable (facetRelative j) := by
  apply Measurable.of_eval
  intro i
  by_cases hi : i ≠ j
  · simpa [facetRelative,hi] using (measurable_pi_apply (Sum.inr ⟨i,hi⟩ : WinnerFacet j))
  · simp [facetRelative,hi]

theorem measurableSet_facetWinnerRegion {k : ℕ} (j : Fin k) :
    MeasurableSet (facetWinnerRegion j) := by
  rw [show facetWinnerRegion j =
    ⋂ i : {i : Fin k // i ≠ j}, {z | if i.val < j then z i.val < 0 else z i.val ≤ 0} by
    ext z; simp [facetWinnerRegion]]
  apply MeasurableSet.iInter
  intro i
  by_cases hi : i.val < j
  · simpa [hi] using measurableSet_lt (measurable_pi_apply i.val) (measurable_const (a:=(0:ℝ)))
  · simpa [hi] using measurableSet_le (measurable_pi_apply i.val) (measurable_const (a:=(0:ℝ)))

/-- A facet vector whose signed baseline entries are negatives of each other
describes the exact Gaussian thin window on its base and relative scores. -/
theorem shifted_facet_window_ae {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {k : ℕ} (j : Fin k) (Z : Ω → WinnerFacet j → ℝ)
    (h r : ℝ) (hsign : ∀ᵐ w ∂μ, Z w (.inl false) = -Z w (.inl true)) :
    faceEvent Z (winnerFacetStrict j) (winnerFacetThreshold j h r) 0 =ᵐ[μ]
      weightedWindow (fun w ↦ Z w (.inl true)-h) 0 r ∩
        (facetRelative j ∘ Z) ⁻¹' facetWinnerRegion j := by
  filter_upwards [hsign] with w hw
  change (∀ b, facePass (winnerFacetStrict j b) (Z w b)
    (winnerFacetThreshold j h r b + 0)) ↔
      (0 < Z w (.inl true)-h ∧ Z w (.inl true)-h ≤ 0+r) ∧
        (∀ i : Fin k, i ≠ j → if i < j then facetRelative j (Z w) i < 0 else
          facetRelative j (Z w) i ≤ 0)
  simp only [add_zero,zero_add]
  constructor
  · intro hs
    refine ⟨⟨?_,?_⟩,?_⟩
    · have hx := hs (.inl false)
      simpa [winnerFacetStrict,winnerFacetThreshold,facePass,hw,sub_pos] using hx
    · have hx := hs (.inl true)
      simp only [winnerFacetStrict,winnerFacetThreshold,facePass,Bool.false_eq_true,if_false] at hx
      linarith
    · intro i hi
      by_cases hil : i<j <;> simpa [facetRelative,hi,hil,winnerFacetStrict,
        winnerFacetThreshold,facePass] using hs (.inr ⟨i,hi⟩)
  · rintro ⟨⟨hlo,hhi⟩,hh⟩ b
    rcases b with b | i
    · cases b
      · simpa [winnerFacetStrict,winnerFacetThreshold,facePass,hw,sub_pos] using hlo
      · simp only [winnerFacetStrict,winnerFacetThreshold,facePass,Bool.false_eq_true,if_false]
        linarith
    · by_cases hil : i.val<j <;> simpa [facetRelative,i.property,hil,winnerFacetStrict,
        winnerFacetThreshold,facePass] using hh i.val i.property

end CubeSqrtProbability
#print axioms CubeSqrtProbability.shifted_facet_window_ae

namespace CubeSqrtProbability

/-- Transfer the quantitative true-source/Gaussian facet error to the exact
Esscher weighted event; the constant is unchanged. -/
theorem weighted_error_of_facet_error
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure Ω') [IsProbabilityMeasure ν]
    {k : ℕ} (j : Fin k) (h : ℝ)
    (Z : Ω → WinnerFacet j → ℝ) (Z' : Ω' → WinnerFacet j → ℝ)
    (hm : Measurable Z) (hm' : Measurable Z')
    (hs : ∀ᵐ w ∂μ, Z w (.inl false) = -Z w (.inl true))
    (hs' : ∀ᵐ w ∂ν, Z' w (.inl false) = -Z' w (.inl true))
    (ε : ℝ)
    (hε : ∀ r > 0,
      |μ.real (faceEvent Z (winnerFacetStrict j) (winnerFacetThreshold j h r) 0) -
        ν.real (faceEvent Z' (winnerFacetStrict j) (winnerFacetThreshold j h r) 0)| ≤ ε) :
    |winnerFaceWeight μ (fun w ↦ Z w (.inl true)-h) (facetRelative j ∘ Z) (facetWinnerRegion j) -
      winnerFaceWeight ν (fun w ↦ Z' w (.inl true)-h) (facetRelative j ∘ Z')
        (facetWinnerRegion j)| ≤ ε := by
  apply weighted_winner_face_comparison μ ν _ _ _ _
    (((measurable_pi_apply _).comp hm).sub_const h) ((measurable_facetRelative j).comp hm)
    (((measurable_pi_apply _).comp hm').sub_const h) ((measurable_facetRelative j).comp hm')
    _ _ (measurableSet_facetWinnerRegion j) (measurableSet_facetWinnerRegion j) ε
  intro r hr
  simp only [Function.comp_apply]
  rw [← measureReal_congr (shifted_facet_window_ae μ j Z h r hs),
    ← measureReal_congr (shifted_facet_window_ae ν j Z' h r hs')]
  exact hε r hr

end CubeSqrtProbability
#print axioms CubeSqrtProbability.weighted_error_of_facet_error
