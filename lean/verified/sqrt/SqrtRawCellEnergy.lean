import SqrtMidpointWholePeriod

namespace CenteredCubeSqrt
open MeasureTheory Set
open scoped Interval BigOperators
set_option maxHeartbeats 1600000

noncomputable def cellPrimitive (u r : ℝ) : ℝ := (if u≤r then 1 else 0)-r

theorem cellPrimitive_continuous_left {u : ℝ} (_hu : 0≤u) :
    EqOn (fun r => (cellPrimitive u r)^2) (fun r : ℝ => r^2) (Ioo 0 u) := by
  intro r hr
  simp only [cellPrimitive]
  rw [ite_eq_right hr.2.not_ge,zero_sub,neg_sq]

theorem cellPrimitive_continuous_right {u : ℝ} (_hu : u≤1) :
    EqOn (fun r => (cellPrimitive u r)^2) (fun r : ℝ => (1-r)^2) (Ioo u 1) := by
  intro r hr
  simp only [cellPrimitive]
  rw [ite_eq_left hr.1.le]

theorem cellPrimitive_energy {u : ℝ} (hu : u ∈ Icc (0:ℝ) 1) :
    (∫ r in (0:ℝ)..1,(cellPrimitive u r)^2)=u^2-u+1/3 := by
  let F (r : ℝ) := (cellPrimitive u r)^2
  have hleft := cellPrimitive_continuous_left hu.1
  have hright := cellPrimitive_continuous_right hu.2
  have ic : Continuous (fun r : ℝ => (1-r)^2) := by fun_prop
  have a : IntervalIntegrable F volume 0 u := by
    apply (intervalIntegrable_congr_uIoo (f:=F) (g:=fun r : ℝ => r^2) _).2
      ((continuous_id.pow 2).intervalIntegrable _ _)
    rw [uIoo_of_le hu.1]
    exact hleft
  have b : IntervalIntegrable F volume u 1 := by
    apply (intervalIntegrable_congr_uIoo (f:=F) (g:=fun r : ℝ => (1-r)^2) _).2
      (ic.intervalIntegrable _ _)
    rw [uIoo_of_le hu.2]
    exact hright
  change (∫ r in (0:ℝ)..1,F r)=_
  rw [←intervalIntegral.integral_add_adjacent_intervals a b,
    intervalIntegral.integral_congr_Ioo_of_le hu.1 hleft,
    intervalIntegral.integral_congr_Ioo_of_le hu.2 hright]
  have h := intervalIntegral.integral_comp_sub_left (f:=fun r : ℝ => r^2) (a:=u) (b:=1) (1:ℝ)
  change (∫ x in u..1,(1-x)^2)=(∫ x in 1-1..1-u,x^2) at h
  rw [sub_self] at h
  rw [h,integral_pow,integral_pow]
  norm_num
  ring

noncomputable def labelCellMidpoint {B : ℕ} (y : Fin B) : ℝ := ((y.val:ℝ)+1/2)/(B:ℝ)

theorem labelCellMidpoint_mem {B : ℕ} (y : Fin B) :
    labelCellMidpoint y ∈ Icc (0:ℝ) 1 := by
  have hB : 0<(B:ℝ) := by exact_mod_cast (show 0<B by have := y.isLt; omega)
  have hy : (y.val:ℝ)+1≤B := by exact_mod_cast (Nat.succ_le_of_lt y.isLt)
  unfold labelCellMidpoint
  exact ⟨by positivity,(div_le_one hB).mpr (by linarith)⟩

theorem label_cell_energy {B : ℕ} (y : Fin B) :
    (∫ r in (0:ℝ)..1,(cellPrimitive (labelCellMidpoint y) r)^2)=
      (labelCellMidpoint y)^2-labelCellMidpoint y+1/3 :=
  cellPrimitive_energy (labelCellMidpoint_mem y)

theorem label_zero_energy_le_third {B : ℕ} (hB : 0<B) :
    (∫ r in (0:ℝ)..1,(cellPrimitive (labelCellMidpoint (⟨0,hB⟩ : Fin B)) r)^2)≤1/3 := by
  let u := labelCellMidpoint (⟨0,hB⟩ : Fin B)
  have hu := labelCellMidpoint_mem (⟨0,hB⟩ : Fin B)
  rw [label_cell_energy]
  have h := mul_le_of_le_one_right hu.1 hu.2
  nlinarith

#print axioms label_cell_energy
#print axioms label_zero_energy_le_third

end CenteredCubeSqrt
