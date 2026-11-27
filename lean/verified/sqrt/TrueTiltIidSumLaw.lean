import TrueTiltProductLaw
import SumLawTransfer

open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace CubeSqrtProbability

/-- The law of the score sum in the genuine, tilted n-coordinate source is
the n-fold sum of its actual normalized tilted one-coordinate score law.
This permits any finite score transformation, including centered facets. -/
theorem true_product_tilt_score_sumLaw
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    [AddCommMonoid E] [MeasurableAdd₂ E]
    (P : Measure Ω) [IsProbabilityMeasure P] (f : Ω → ℝ)
    (hf : Integrable (fun w ↦ Real.exp (f w)) P)
    (G : Ω → E) (hG : Measurable G) (n : ℕ) :
    ((Measure.pi (fun _ : Fin n ↦ P)).tilted (fun x ↦ ∑ i, f (x i))).map
      (fun x ↦ ∑ i, G (x i)) = sumLaw ((P.tilted f).map G) n := by
  rw [true_product_tilt_eq_general P f hf]
  let Q := P.tilted f
  haveI : IsProbabilityMeasure Q := isProbabilityMeasure_tilted hf
  change (Measure.pi (fun _ : Fin n ↦ Q)).map (fun x ↦ ∑ i, G (x i)) =
    sumLaw (Q.map G) n
  let X (i : Fin n) (x : Fin n → Ω) := G (x i)
  have ind : iIndepFun X (Measure.pi (fun _ : Fin n ↦ Q)) :=
    iIndepFun_pi (fun _ ↦ hG.aemeasurable)
  have hm (i : Fin n) : Measurable (X i) := hG.comp (measurable_pi_apply i)
  have hl (i : Fin n) : (Measure.pi (fun _ : Fin n ↦ Q)).map (X i) = Q.map G := by
    change (Measure.pi (fun _ : Fin n ↦ Q)).map (G ∘ fun x ↦ x i) = _
    rw [← Measure.map_map hG (measurable_pi_apply i),Measure.pi_map_eval]
    simp
  simpa [X] using sumLaw_of_actual_iid (Measure.pi (fun _ : Fin n ↦ Q)) (Q.map G)
    X ind hm hl Finset.univ

end CubeSqrtProbability
#print axioms CubeSqrtProbability.true_product_tilt_score_sumLaw
