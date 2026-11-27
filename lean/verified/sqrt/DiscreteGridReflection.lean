import DiscreteReflection

open MeasureTheory ProbabilityTheory Set
open scoped NNReal Function
namespace CubeBrownian

theorem firstCross_pairwise {n : ℕ} (a : ℝ) :
    Pairwise (Disjoint on (firstCross (n:=n) a)) := by
  intro i j hij
  rw [Function.onFun, Set.disjoint_left]
  intro x hi hj
  rcases lt_or_gt_of_ne hij with h | h
  · exact (not_lt_of_ge (hj.2 i h)) hi.1
  · exact (not_lt_of_ge (hi.2 j h)) hj.1

theorem firstCross_iUnion {n : ℕ} (a : ℝ) :
    (⋃ k, firstCross (n:=n) a k) = {x | ∃ k, a < partialSum k x} := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨k,hk⟩ := mem_iUnion.mp hx
    exact ⟨k,hk.1⟩
  · intro hx
    change ∃ k, a < partialSum k x at hx
    refine mem_iUnion.mpr ⟨Nat.find hx,Nat.find_spec hx,?_⟩
    intro j hj
    exact le_of_not_gt (Nat.find_min hx hj)

theorem firstCross_grid_endpoint_CDF {n : ℕ} (v : Fin n → ℝ≥0) (a z : ℝ)
    (A : (Fin n → ℝ) → ℝ)
    (hA : ∀ k x, x ∈ firstCross a k → A x = partialSum k x) :
    let P := Measure.pi (fun i ↦ gaussianReal 0 (v i))
    let E : Set (Fin n → ℝ) := {x | ∃ k, a < partialSum k x}
    P (E ∩ {x | (∑ i, x i) ≤ z}) = P (E ∩ {x | 2*A x - ∑ i, x i ≤ z}) := by
  dsimp only
  rw [← firstCross_iUnion a, iUnion_inter, iUnion_inter]
  let F : (Fin n → ℝ) → ℝ := fun x ↦ ∑ i, x i
  have hF : Measurable F := Finset.measurable_fun_sum _ (fun i _ ↦ measurable_pi_apply i)
  have hpiece (k : ℕ) : firstCross (n:=n) a k ∩ {x | 2*A x - ∑ i, x i ≤ z} =
      firstCross a k ∩ {x | 2*partialSum k x - ∑ i, x i ≤ z} := by
    ext x
    by_cases hx : x ∈ firstCross (n:=n) a k <;> simp [hx, hA k x]
  have hG (k : ℕ) : Measurable (fun x : Fin n → ℝ ↦ 2*partialSum k x - ∑ i, x i) :=
    (measurable_const.mul (measurable_partialSum k)).sub hF
  have hd (S : ℕ → Set (Fin n → ℝ)) :
      Pairwise (Disjoint on fun k ↦ firstCross a k ∩ S k) := by
    intro i j hij
    exact (firstCross_pairwise (n:=n) a hij).mono inter_subset_left inter_subset_left
  simp_rw [hpiece]
  rw [measure_iUnion (hd _) (fun k ↦ (measurable_firstCross a k).inter
         (measurableSet_le hF measurable_const)),
      measure_iUnion (hd _) (fun k ↦ (measurable_firstCross a k).inter
         (measurableSet_le (hG k) measurable_const))]
  apply tsum_congr
  intro k
  have he := congrArg (fun P : Measure ℝ ↦ P (Iic z)) (firstCross_endpoint_reflection v a k)
  rw [Measure.map_apply hF measurableSet_Iic,
      Measure.map_apply (hG k) measurableSet_Iic,
      Measure.restrict_apply (hF measurableSet_Iic),
      Measure.restrict_apply ((hG k) measurableSet_Iic),
      inter_comm _ (firstCross a k), inter_comm _ (firstCross a k)] at he
  exact he
end CubeBrownian
#print axioms CubeBrownian.firstCross_grid_endpoint_CDF
