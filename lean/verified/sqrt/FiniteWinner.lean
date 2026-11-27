import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Order.ConditionallyCompleteLattice.Finset
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
namespace CubeBrownian

def finiteWinner {Ω : Type*} {n : ℕ} (X : Fin n → Ω → ℝ) (j : Fin n) : Set Ω :=
  {w | (∀ i, X i w ≤ X j w) ∧ ∀ i < j, X i w < X j w}

theorem measurableSet_finiteWinner {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (X : Fin n → Ω → ℝ) (hm : ∀ i, Measurable (X i)) (j : Fin n) :
    MeasurableSet (finiteWinner X j) := by
  have he : finiteWinner X j =
      (⋂ i : Fin n, {w | X i w ≤ X j w}) ∩ (⋂ i : Fin n, {w | i < j → X i w < X j w}) := by
    ext w
    simp only [finiteWinner,mem_ofPred_eq,mem_inter_iff,mem_iInter]
  rw [he]
  refine (MeasurableSet.iInter fun i ↦ measurableSet_le (hm i) (hm j)).inter (MeasurableSet.iInter fun i ↦ ?_)
  by_cases h : i < j
  · simpa only [h,true_imp_iff] using measurableSet_lt (hm i) (hm j)
  · simp [h]

theorem existsUnique_finiteWinner {Ω : Type*} {n : ℕ} (hn : 0 < n)
    (X : Fin n → Ω → ℝ) (w : Ω) : ∃! j, w ∈ finiteWinner X j := by
  classical
  let _ : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  let p (m : ℕ) := ∃ j : Fin n, (j:ℕ) = m ∧ X j w = ⨆ i, X i w
  have hp : ∃ m, p m := by
    obtain ⟨j,hj⟩ := exists_eq_ciSup_of_finite (f := fun i : Fin n ↦ X i w)
    exact ⟨j,j,rfl,hj⟩
  obtain ⟨j,hj,hMax⟩ := Nat.find_spec hp
  have hW : w ∈ finiteWinner X j := by
    refine ⟨fun i ↦ hMax.symm ▸ le_ciSup (finite_range (fun i ↦ X i w)).bddAbove i,?_⟩
    intro i hi
    have hle : X i w ≤ X j w := hMax.symm ▸ le_ciSup (finite_range (fun i ↦ X i w)).bddAbove i
    apply lt_of_le_of_ne hle
    intro h
    have hJ : (i:ℕ) < Nat.find hp := by rwa [← hj]
    exact Nat.find_min hp hJ ⟨i,rfl,h.trans hMax⟩
  refine ⟨j,hW,fun i hi ↦ ?_⟩
  by_contra! hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact (not_lt_of_ge (hi.1 j)) (hW.2 i h)
  · exact (not_lt_of_ge (hW.1 i)) (hi.2 j h)

theorem finiteWinner_eq_sup {Ω : Type*} {n : ℕ}
    (X : Fin n → Ω → ℝ) {w : Ω} {j : Fin n} (hj : w ∈ finiteWinner X j) :
    X j w = ⨆ i, X i w := by
  let _ : Nonempty (Fin n) := ⟨j⟩
  exact le_antisymm (le_ciSup (finite_range (fun i ↦ X i w)).bddAbove j) (ciSup_le hj.1)

theorem finiteWinner_tilted_sum_expMax {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {n : ℕ} (hn : 0 < n)
    (X : Fin n → Ω → ℝ) (hm : ∀ i, Measurable (X i))
    (hNorm : ∀ i, ∫ w, Real.exp (X i w) ∂μ = 1) :
    (∑ j, (μ.tilted (X j)) (finiteWinner X j)) =
      ∫⁻ w, ENNReal.ofReal (Real.exp (⨆ i, X i w)) ∂μ := by
  classical
  let W (j : Fin n) := finiteWinner X j
  let D (j : Fin n) (w : Ω) := ENNReal.ofReal (Real.exp (X j w))
  let F j := (W j).indicator (D j)
  have hmW j : MeasurableSet (W j) := measurableSet_finiteWinner X hm j
  have hmD j : Measurable (D j) := ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (hm j))
  have hmF j : Measurable (F j) := (hmD j).indicator (hmW j)
  have htilt (j : Fin n) : (μ.tilted (X j)) (W j) = ∫⁻ w, F j w ∂μ := by
    rw [tilted_apply' _ _ (hmW j),hNorm,lintegral_indicator (hmW j)]
    simp only [div_one,D]
  have hPoint (w : Ω) : (∑ j, F j w) = ENNReal.ofReal (Real.exp (⨆ i, X i w)) := by
    obtain ⟨j,hj,hU⟩ := existsUnique_finiteWinner hn X w
    rw [Finset.sum_eq_single j]
    · rw [show F j w = D j w from indicator_of_mem hj _]
      change ENNReal.ofReal (Real.exp (X j w)) = _
      rw [finiteWinner_eq_sup X hj]
    · intro i _ hi
      apply indicator_of_notMem
      intro hw
      exact hi (hU i hw)
    · intro hj
      exact (hj (Finset.mem_univ j)).elim
  change (∑ j, (μ.tilted (X j)) (W j)) = _
  simp_rw [htilt]
  rw [← lintegral_finsetSum _ (fun j _ ↦ hmF j)]
  exact lintegral_congr hPoint

end CubeBrownian
#print axioms CubeBrownian.finiteWinner_tilted_sum_expMax
