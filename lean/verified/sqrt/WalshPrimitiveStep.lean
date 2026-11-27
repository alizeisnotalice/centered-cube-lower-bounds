import WalshBalanced
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace CenteredCubeSqrt
open MeasureTheory Set Classical
open scoped BigOperators Interval
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem ordinalWalsh_eq_nat {b : ℕ} (a : NonzeroBinary b) (y : Fin (2^b)) :
    ordinalWalsh a y = walshNat a.1 y.val := by
  unfold walshNat ordinalWalsh binaryWalsh
  simp only [Nat.mod_eq_of_lt y.isLt]

theorem ordinalWalsh_sum_zero {b : ℕ} (a : NonzeroBinary b) :
    ∑ y : Fin (2^b), ordinalWalsh a y = 0 := by
  simp_rw [ordinalWalsh_eq_nat]
  rw [Fin.sum_univ_eq_sum_range]
  exact walshPrefix_end_zero_of_nonzero a.1 a.2

theorem walshCellPrimitive_eq_count {b : ℕ} (a : NonzeroBinary b) (r : ℝ) :
    walshCellPrimitive a r =
      (∑ y : Fin (2^b), if labelCellMidpoint y ≤ r then ordinalWalsh a y else 0) / (2:ℝ)^b := by
  unfold walshCellPrimitive
  simp only [cellPrimitive, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
    ordinalWalsh_sum_zero, zero_mul, sub_zero]
  congr 1
  apply Finset.sum_congr rfl
  intro y _
  split <;> simp_all

noncomputable def walshThreshold (b j : ℕ) : ℝ :=
  ((j:ℝ)+1/2)/(2:ℝ)^b

theorem walshCellPrimitive_from_cut {b : ℕ} (a : NonzeroBinary b) (r : ℝ)
    (j : ℕ) (hj : j ≤ 2^b)
    (hcut : ∀ k : ℕ, k < 2^b → (walshThreshold b k ≤ r ↔ k < j)) :
    walshCellPrimitive a r = walshPrefix a.1 j / (2:ℝ)^b := by
  rw [walshCellPrimitive_eq_count]
  simp_rw [ordinalWalsh_eq_nat, show ∀ y : Fin (2^b), labelCellMidpoint y = walshThreshold b y.val by
    intro y; unfold labelCellMidpoint walshThreshold; push_cast; rfl]
  have e : (∑ y : Fin (2^b), if walshThreshold b y.val ≤ r then walshNat a.1 y.val else 0) =
      ∑ y : Fin (2^b), if y.val < j then walshNat a.1 y.val else 0 := by
    apply Finset.sum_congr rfl
    intro y _
    simp only [hcut y.val y.isLt]
  rw [e, Fin.sum_univ_eq_sum_range (fun y : ℕ => if y < j then walshNat a.1 y else 0) (2^b), ←Finset.sum_filter]
  have s : ((Finset.range (2^b)).filter fun x => x < j) = Finset.range j := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨fun h => h.2,fun h => ⟨h.trans_le hj,h⟩⟩
  rw [s]
  rfl

theorem walshCellPrimitive_mid_step {b : ℕ} (a : NonzeroBinary b) (r : ℝ)
    (j : ℕ) (hj : j < 2^b) (hr : r ∈ Ico (walshThreshold b j) (walshThreshold b (j+1))) :
    walshCellPrimitive a r = walshPrefix a.1 (j+1) / (2:ℝ)^b := by
  apply walshCellPrimitive_from_cut a r (j+1) hj
  intro k _
  constructor
  · intro hk
    by_contra H
    have hk' : ((j+1:ℕ):ℝ) ≤ k := by exact_mod_cast Nat.le_of_not_gt H
    have hmon : walshThreshold b (j+1) ≤ walshThreshold b k :=
      div_le_div_of_nonneg_right (by linarith) (by positivity)
    exact not_lt_of_ge (hmon.trans hk) hr.2
  · intro hk
    have hk' : (k:ℝ) ≤ j := by exact_mod_cast (show k ≤ j by omega)
    exact (div_le_div_of_nonneg_right (by linarith : (k:ℝ)+1/2 ≤ (j:ℝ)+1/2)
      (show 0 ≤ (2:ℝ)^b by positivity)).trans hr.1

#print axioms walshCellPrimitive_mid_step
end CenteredCubeSqrt
