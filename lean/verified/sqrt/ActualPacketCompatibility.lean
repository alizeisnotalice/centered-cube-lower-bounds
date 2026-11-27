import ActualBrownianMeshLower
import ActualPacketWinnerUniform
import FinitePacketEvent
import ActualPacketEndgame
import PaperEventMeasurability
import PaperPairGlobalGap

open Filter Set MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology BigOperators
namespace CenteredCubeSqrt
open CubeBrownian CubeSqrtProbability CubeSqrtOverlap
set_option maxHeartbeats 1800000

theorem actual_paper_product_law_eq (n : ℕ) :
    actualPaperProductLaw n = CenteredCube.sqrtCellLaw n := by
  unfold actualPaperProductLaw CenteredCube.sqrtCellLaw CubeSqrtProbability.unitPeriodLaw
  rfl

theorem paper_packet_prob_eq_union {B K n N : ℕ} [NeZero K]
    (p v P A δ : ℝ) (f : ZMod K → Fin B) (M : ℕ) (i : ℕ) :
    let h := v/2-2
    let score (j : Fin (N+1)) (z : Fin n → ℝ) :=
      ∑ c, Real.log (1+actualWindowPerturbation f M p δ
        (paperPacketLength (K:ℝ) v P A i j) (z c))
    {z | h < ⨆ j, score j z} = actualPaperPacketEvent f M n N p δ h v P A i := by
  intro h score
  simpa only [actualPaperPacketEvent, actualPaperScaleEvent, score] using
    finite_packet_exceedance_eq_iUnion score h

theorem paper_packet_width_value (T w : ℕ) (hw : T^2+4≤w) (hT : 2≤T) :
    let A : ℝ := 1/(T:ℝ)^2
    0<A ∧ (4:ℝ)≤(w:ℝ) ∧ 1/(w:ℝ)≤A ∧ (T^3:ℕ)*A=T := by
  intro A
  have hT0 : 0<(T:ℝ) := by exact_mod_cast (show 0<T by omega)
  have h4 : (4:ℝ)≤w := by exact_mod_cast (show 4≤w by omega)
  have hW0 : 0<(w:ℝ) := by linarith
  have hSq : (T:ℝ)^2≤w := by exact_mod_cast (show T^2≤w by omega)
  refine ⟨by dsimp [A]; positivity,h4,?_,?_⟩
  · unfold A
    exact one_div_le_one_div_of_le (by positivity) hSq
  · unfold A
    push_cast
    field_simp [hT0.ne']

private theorem centered_box_node_value_congr {e₁ e₂ t₁ t₂ : ℝ}
    (he : e₁ = e₂) (ht : t₁ = t₂)
    {he₁ : 0 < e₁} {he₂ : 0 < e₂} {ht₁ : 0 ≤ t₁} {ht₂ : 0 ≤ t₂} :
    centeredBoxNodeL2 e₁ t₁ he₁ ht₁ = centeredBoxNodeL2 e₂ t₂ he₂ ht₂ := by
  subst e₂
  subst t₂
  rfl

theorem canonical_box_grid_reference_eq (T w : ℕ) (hw : T^2+4≤w) (hT : 2≤T) (L : ℝ)
    (hW : (4:ℝ)≤w) (hA : (0:ℝ)<1/(T:ℝ)^2) :
    canonicalFiniteGridExp (paperPacketBoxGrid w (1/(T:ℝ)^2) hW hA (T^3))
      (paperPacketLambda L) = actualSmoothedGridMean T w L := by
  have hW1 : (1:ℝ)≤w := by linarith
  have hGrid :
    paperPacketBoxGrid w (1/(T:ℝ)^2) hW hA (T^3) =
      fun i => centeredBoxNodeL2 (1/max (w:ℝ) 1) (actualPaperGrid T i)
        (by positivity) (NNReal.coe_nonneg (actualPaperGrid T i)) := by
    funext i
    unfold paperPacketBoxGrid
    have htime : (i:ℝ)*(1/(T:ℝ)^2) = (actualPaperGrid T i:ℝ) := by
      unfold actualPaperGrid cellLeft
      push_cast <;> rfl
    exact centered_box_node_value_congr (by rw [max_eq_left hW1]) htime
  have hΛ : paperPacketLambda L = 2*actualPaperKappa L := by
    apply NNReal.coe_injective
    simp only [NNReal.coe_mul,NNReal.coe_ofNat,actualPaperKappa_coe,paperPacketLambda]
    rw [Real.coe_toNNReal _ (by positivity)]
    ring
  unfold actualSmoothedGridMean
  rw [hGrid,hΛ]

#print axioms paper_packet_prob_eq_union
#print axioms canonical_box_grid_reference_eq
end CenteredCubeSqrt
