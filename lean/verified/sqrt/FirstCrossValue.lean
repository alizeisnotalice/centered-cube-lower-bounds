import DiscreteGridReflection
open MeasureTheory Set
open scoped NNReal
namespace CubeBrownian

noncomputable def firstCrossValue {n : ℕ} (a : ℝ) (x : Fin n → ℝ) : ℝ := by
  classical
  exact if h : ∃ k, a < partialSum k x then partialSum (Nat.find h) x else a

theorem firstCrossValue_eq {n : ℕ} {a : ℝ} {k : ℕ} {x : Fin n → ℝ}
    (hx : x ∈ firstCross a k) : firstCrossValue a x = partialSum k x := by
  classical
  have h : ∃ j, a < partialSum j x := ⟨k,hx.1⟩
  rw [firstCrossValue, dif_pos h]
  congr 1
  apply le_antisymm (Nat.find_min' h hx.1)
  by_contra! hlt
  exact (not_lt_of_ge (hx.2 _ hlt)) (Nat.find_spec h)

theorem measurable_firstCrossValue {n : ℕ} (a : ℝ) :
    Measurable (firstCrossValue (n:=n) a) := by
  classical
  intro s hs
  let U := ⋃ k, firstCross (n:=n) a k
  have hU : MeasurableSet U := MeasurableSet.iUnion (measurable_firstCross a)
  have he : firstCrossValue (n:=n) a ⁻¹' s =
      (⋃ k, firstCross a k ∩ partialSum k ⁻¹' s) ∪ (if a ∈ s then Uᶜ else ∅) := by
    ext x
    by_cases hx : x ∈ U
    · have hu := hx
      change x ∈ (⋃ k, firstCross (n:=n) a k) at hu
      obtain ⟨k,hk⟩ := mem_iUnion.mp hu
      constructor
      · intro h
        exact Or.inl (mem_iUnion.mpr ⟨k,hk,by simpa only [mem_preimage,firstCrossValue_eq hk] using h⟩)
      · intro h
        rcases h with h | h
        · obtain ⟨j,hj,hsj⟩ := mem_iUnion.mp h
          simpa only [mem_preimage,firstCrossValue_eq hj] using hsj
        · split at h <;> simp_all
    · have hN : ¬ ∃ k, a < partialSum k x := by
        intro h
        apply hx
        change x ∈ (⋃ k, firstCross (n:=n) a k)
        rw [firstCross_iUnion]
        exact h
      have hN' : ∀ k, x ∉ firstCross (n:=n) a k := fun k hk ↦ hN ⟨k,hk.1⟩
      simp [firstCrossValue, hN, hN', hx]
  rw [he]
  apply (MeasurableSet.iUnion fun k ↦ (measurable_firstCross a k).inter
    ((measurable_partialSum k) hs)).union
  split
  · exact hU.compl
  · exact MeasurableSet.empty
end CubeBrownian
#print axioms CubeBrownian.measurable_firstCrossValue
