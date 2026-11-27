import FiniteWinner
import WeightedTail

open MeasureTheory ProbabilityTheory Set Filter CubeSqrtProbability
open scoped ENNReal Function
namespace CubeBrownian

theorem finiteWinner_threshold_layercake {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ} (hn : 0 < n)
    (X : Fin n → Ω → ℝ) (hm : ∀ i, Measurable (X i))
    (hInt : ∀ i, Integrable (fun w ↦ Real.exp (X i w)) μ)
    (hNorm : ∀ i, ∫ w, Real.exp (X i w) ∂μ = 1) (h : ℝ) :
    ENNReal.ofReal (Real.exp h) * μ {w | h < ⨆ i, X i w} =
      ∑ j, ∫⁻ r : ℝ, expTailWeight r *
        (μ.tilted (X j)) (weightedWindow (X j) h r ∩ finiteWinner X j) := by
  classical
  let W := finiteWinner X
  let S (j : Fin n) := {w | h < X j w}
  let E (j : Fin n) := S j ∩ W j
  have hmW (j : Fin n) : MeasurableSet (W j) := measurableSet_finiteWinner X hm j
  have hmS (j : Fin n) : MeasurableSet (S j) := measurableSet_lt measurable_const (hm j)
  have hmE (j : Fin n) : MeasurableSet (E j) := (hmS j).inter (hmW j)
  have hu : {w | h < ⨆ i, X i w} = ⋃ j, E j := by
    ext w
    constructor
    · intro hw
      obtain ⟨j,hj,_⟩ := existsUnique_finiteWinner hn X w
      have hb : h < X j w := (finiteWinner_eq_sup X hj).symm ▸ hw
      exact mem_iUnion.mpr ⟨j,hb,hj⟩
    · intro hw
      obtain ⟨j,hj,hWj⟩ := mem_iUnion.mp hw
      change h < ⨆ i, X i w
      rw [← finiteWinner_eq_sup X hWj]
      exact hj
  have hd : Pairwise (Disjoint on E) := by
    intro i j hij
    rw [Function.onFun,disjoint_left]
    intro w hi hj
    obtain ⟨k,_,h⟩ := existsUnique_finiteWinner hn X w
    exact hij ((h i hi.2).trans (h j hj.2).symm)
  have hOne (j : Fin n) : ENNReal.ofReal (Real.exp h) * μ (E j) =
      ∫⁻ r : ℝ, expTailWeight r * (μ.tilted (X j)) (weightedWindow (X j) h r ∩ W j) := by
    let Q := μ.tilted (X j)
    let _ : IsProbabilityMeasure Q := isProbabilityMeasure_tilted (hInt j)
    have H := weighted_tail_layercake (Q.restrict (W j)) (hm j) h
    simp_rw [Measure.restrict_apply (weightedWindow_measurable (hm j) h _)] at H
    change _ = ∫⁻ r : ℝ, expTailWeight r * Q (weightedWindow (X j) h r ∩ W j)
    rw [← H]
    change _ = ∫⁻ w, expTailWeight (X j w-h) ∂((Q.restrict (W j)).restrict (S j))
    rw [Measure.restrict_restrict (hmS j)]
    unfold Q Measure.tilted
    simp only [hNorm,div_one]
    have hf : Measurable (fun w ↦ ENNReal.ofReal (Real.exp (X j w))) :=
      (Real.measurable_exp.comp (hm j)).ennreal_ofReal
    have hg : Measurable (fun w ↦ expTailWeight (X j w-h)) :=
      expTailWeight_measurable.comp ((hm j).sub_const h)
    rw [setLIntegral_withDensity_eq_setLIntegral_mul μ hf hg (hmE j)]
    have he (w : Ω) : ENNReal.ofReal (Real.exp (X j w))*expTailWeight (X j w-h) =
        ENNReal.ofReal (Real.exp h) := by
      unfold expTailWeight
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,← Real.exp_add]
      congr 2
      ring
    simp_rw [Pi.mul_apply,he]
    rw [lintegral_const,Measure.restrict_apply MeasurableSet.univ, univ_inter]
  rw [hu,measure_iUnion hd hmE,tsum_fintype,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact hOne j

end CubeBrownian
#print axioms CubeBrownian.finiteWinner_threshold_layercake
