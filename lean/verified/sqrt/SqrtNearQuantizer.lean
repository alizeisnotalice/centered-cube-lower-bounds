import SqrtActualMidpointPrefix
namespace CenteredCubeSqrt
open MeasureTheory Set
open scoped Interval BigOperators
set_option maxHeartbeats 1000000

theorem cell_same_label_product_formula (u r θ : ℝ) (hθ : 0≤θ) :
    cellPrimitive u r*cellPrimitive u (r+θ) =
      r*(1-r-θ)+(1-r-θ)*cellPrimitive u r-r*cellPrimitive u (r+θ) := by
  unfold cellPrimitive
  by_cases h : u≤r
  · rw [ite_eq_left h,ite_eq_left (show u≤r+θ by linarith)]
    ring
  · rw [ite_eq_right h]
    split <;> ring

theorem same_label_pair_mean_exact {B : ℕ} (hB : 0<B) (r θ : ℝ) (hθ : 0≤θ) :
    (1/(B:ℝ))*(∑ y : Fin B,cellPrimitive (labelCellMidpoint y) r*cellPrimitive (labelCellMidpoint y) (r+θ)) =
      r*(1-r-θ)+(1-r-θ)*midpointError B r-r*midpointError B (r+θ) := by
  have hb : (B:ℝ) ≠ 0 := by exact_mod_cast hB.ne'
  simp_rw [cell_same_label_product_formula _ _ _ hθ]
  rw [Finset.sum_sub_distrib,Finset.sum_add_distrib,←Finset.mul_sum,←Finset.mul_sum,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
    ←cellPrimitive_label_mean hB r,←cellPrimitive_label_mean hB (r+θ)]
  field_simp
  rw [←Finset.mul_sum]

theorem midpointError_abs_le_half_cell {B : ℕ} (hB : 0<B) {x : ℝ} (hx : x∈Icc (0:ℝ) 1) :
    |midpointError B x|≤1/(2*(B:ℝ)) := by
  have hB0 : 0<(B:ℝ) := by exact_mod_cast hB
  have hxA : ∃ j : ℕ, j<B ∧ ∃ r∈Icc (0:ℝ) 1, x=((j:ℝ)+r)/(B:ℝ) := by
    rcases lt_or_eq_of_le hx.2 with hx1|hx1
    · let k : ℤ := ⌊(B:ℝ)*x⌋
      let j := k.toNat
      have hkn : 0≤k := Int.floor_nonneg.mpr (mul_nonneg hB0.le hx.1)
      have hc : (j:ℤ)=k := Int.toNat_of_nonneg hkn
      have hcr : (j:ℝ)=(k:ℝ) := by exact_mod_cast hc
      have hj : j<B := by
        have h : (j:ℝ)<(B:ℝ) := by
          rw [hcr]
          exact (Int.floor_le ((B:ℝ)*x)).trans_lt (by nlinarith [mul_lt_mul_of_pos_left hx1 hB0])
        exact_mod_cast h
      let t := (B:ℝ)*x-(j:ℝ)
      have htl : x=((j:ℝ)+t)/(B:ℝ) := by dsimp [t]; field_simp; ring
      have ht : t∈Icc (0:ℝ) 1 := by
        dsimp only [t]
        rw [hcr]
        exact ⟨by linarith [Int.floor_le ((B:ℝ)*x)],
          by linarith [Int.lt_floor_add_one ((B:ℝ)*x)]⟩
      exact ⟨j,hj,t,ht,htl⟩
    · refine ⟨B-1,by omega,1,by norm_num,?_⟩
      rw [hx1,Nat.cast_sub (Nat.succ_le_of_lt hB),Nat.cast_one,sub_add_cancel,div_self hB0.ne']
  obtain ⟨j,hj,r,hr,hx'⟩ := hxA
  rw [hx']
  exact midpointError_abs_in_cell hj hr

#print axioms same_label_pair_mean_exact
#print axioms midpointError_abs_le_half_cell
end CenteredCubeSqrt
