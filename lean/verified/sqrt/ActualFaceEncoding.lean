import SmoothFaceComparison

open MeasureTheory ProbabilityTheory Set
namespace CubeSqrtProbability

abbrev WinnerFacet {k : ℕ} (j : Fin k) := Bool ⊕ { i : Fin k // i ≠ j }

def winnerFacetStrict {k : ℕ} (j : Fin k) : WinnerFacet j → Bool
  | .inl false => true
  | .inl true => false
  | .inr i => decide (i.val < j)

def winnerFacetThreshold {k : ℕ} (j : Fin k) (h r : ℝ) : WinnerFacet j → ℝ
  | .inl false => -h
  | .inl true => h+r
  | .inr _ => 0

def winnerFacetScore {k : ℕ} (j : Fin k) (x : Fin k → ℝ) : WinnerFacet j → ℝ
  | .inl false => -x j
  | .inl true => x j
  | .inr i => x i.val-x j

theorem measurable_winnerFacetScore {k : ℕ} (j : Fin k) :
    Measurable (winnerFacetScore j) := by
  apply measurable_pi_lambda
  intro i
  rcases i with b | i
  · cases b
    · exact (measurable_pi_apply j).neg
    · exact measurable_pi_apply j
  · exact (measurable_pi_apply i.val).sub (measurable_pi_apply j)

/-- The strict lower threshold, closed upper threshold and smallest-index
winner tie rule are exactly the polyhedral event used by smooth replacement.
The self comparison is omitted from the facet type. -/
theorem winnerFacet_event {Ω : Type*} {k : ℕ} (j : Fin k) (h r : ℝ)
    (X : Ω → Fin k → ℝ) :
    faceEvent (fun w ↦ winnerFacetScore j (X w)) (winnerFacetStrict j)
      (winnerFacetThreshold j h r) 0 =
    {w | h < X w j ∧ X w j ≤ h+r ∧
      ∀ i : Fin k, i ≠ j → if i < j then X w i-X w j < 0 else X w i-X w j ≤ 0} := by
  ext w
  change (∀ i : WinnerFacet j, facePass (winnerFacetStrict j i)
    (winnerFacetScore j (X w) i) (winnerFacetThreshold j h r i+0)) ↔ _
  simp only [mem_setOf_eq, add_zero]
  constructor
  · intro hw
    refine ⟨?_, ?_, ?_⟩
    · simpa [winnerFacetStrict,winnerFacetScore,winnerFacetThreshold,facePass] using hw (.inl false)
    · simpa [winnerFacetStrict,winnerFacetScore,winnerFacetThreshold,facePass] using hw (.inl true)
    · intro i hij
      by_cases hlt : i<j <;>
        simpa [winnerFacetStrict,winnerFacetScore,winnerFacetThreshold,facePass,hlt] using
          hw (.inr ⟨i,hij⟩)
  · rintro ⟨hlo,hhi,hwin⟩ i
    rcases i with b | i
    · cases b
      · simpa [winnerFacetStrict,winnerFacetScore,winnerFacetThreshold,facePass] using hlo
      · simpa [winnerFacetStrict,winnerFacetScore,winnerFacetThreshold,facePass] using hhi
    · by_cases hlt : i.val<j <;>
        simpa [winnerFacetStrict,winnerFacetScore,winnerFacetThreshold,facePass,hlt] using
          hwin i.val i.property

end CubeSqrtProbability
#print axioms CubeSqrtProbability.winnerFacet_event
