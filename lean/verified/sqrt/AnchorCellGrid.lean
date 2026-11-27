import LocalGridTransport
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
namespace CubeBrownian

theorem pi_injective_projection {ι κ : Type*} [Fintype ι] [Fintype κ]
    (P : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (P i)]
    (e : κ → ι) (he : Function.Injective e) :
    (Measure.pi P).map (fun (x : ι → ℝ) k ↦ x (e k)) = Measure.pi (P ∘ e) := by
  have hI : iIndepFun (fun i (x : ι → ℝ) ↦ x i) (Measure.pi P) :=
    iIndepFun_pi (fun i ↦ (measurable_id : Measurable (fun x : ℝ ↦ x)).aemeasurable)
  rw [(hI.precomp he).map_fun_eq_pi_map (fun k ↦ (measurable_pi_apply (e k)).aemeasurable)]
  simp only [fun k ↦ (measurePreserving_eval P (e k)).map_eq]
  rfl

noncomputable def anchorCellTimes (anchor left A : ℝ≥0) (r k : ℕ) : ℝ≥0 :=
  if k = 0 then 0 else if k = 1 then min anchor left
  else if k ≤ (2:ℕ)^r+2 then left + dyadicT A r (k-2) else max anchor (left+A)

theorem anchorCellTimes_mono (anchor left A : ℝ≥0) (r : ℕ) :
    Monotone (anchorCellTimes anchor left A r) := by
  apply monotone_nat_of_le_succ
  intro k
  rcases k with _ | k
  · simp [anchorCellTimes]
  rcases k with _ | k
  · simp [anchorCellTimes,dyadicT_zero]
  · have hK : k+1+1 ≠ 0 ∧ k+1+1 ≠ 1 ∧ k+1+1+1 ≠ 0 ∧ k+1+1+1 ≠ 1 := by omega
    simp only [anchorCellTimes, hK.1, hK.2.1, hK.2.2.1, hK.2.2.2, ite_false]
    split_ifs with h1 h2 h2
    · gcongr
      exact dyadicT_mono A r (by omega)
    · have h := dyadicT_mono A r (by omega : k+1+1-2 ≤ 2^r)
      rw [dyadicT_last] at h
      exact (add_le_add_right h left).trans (le_max_right ..)
    · omega
    · exact le_rfl

theorem anchorCellTimes_offset (anchor left A : ℝ≥0) (r k : ℕ) (hk : k ≤ 2^r) :
    anchorCellTimes anchor left A r (k+2) = left+dyadicT A r k := by
  simp only [anchorCellTimes,
    ite_eq_right (by omega : k+2 ≠ 0), ite_eq_right (by omega : k+2 ≠ 1),
    ite_eq_left (by omega : k+2 ≤ 2^r+2), Nat.add_sub_cancel]

noncomputable def anchorCellIndex (anchor left : ℝ≥0) (r : ℕ) : Fin (2^r+4) :=
  if anchor ≤ left then ⟨1,by exact (by decide : (1:ℕ) < 4).trans_le (Nat.le_add_left 4 (2^r))⟩
  else ⟨2^r+3,by omega⟩

theorem anchorCellTimes_anchor {anchor left A : ℝ≥0} (r : ℕ)
    (h : anchor ≤ left ∨ left+A ≤ anchor) :
    anchorCellTimes anchor left A r (anchorCellIndex anchor left r) = anchor := by
  by_cases hL : anchor ≤ left
  · simp [anchorCellIndex,hL,anchorCellTimes]
  · have hR := h.resolve_left hL
    simp [anchorCellIndex,hL,anchorCellTimes,max_eq_left hR]
end CubeBrownian
#print axioms CubeBrownian.anchorCellTimes_anchor
