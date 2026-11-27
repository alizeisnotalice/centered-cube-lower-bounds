import SqrtActualAtomDiscrepancy
import SqrtRawCellExtended
namespace CenteredCubeSqrt
open MeasureTheory Set
open scoped Interval BigOperators
set_option maxHeartbeats 900000

theorem actualBoxSum_eq_ownBox_on_cell {B K : ℕ} [NeZero K] (hB : 0<B)
    (hK : 2≤K) (f : ZMod K → Fin B) {δ : ℝ}
    (hδ0 : 0<δ) (hδ : δ<1/((B:ℝ)*K)) (k : ℤ) (y : ℝ)
    (hy : y∈Icc ((k:ℝ)/(K:ℝ)) (((k:ℝ)+1)/(K:ℝ))) :
    atomBoxSum f δ y =
      boxWindowDensity δ (y-(((k:ℝ)+labelCellMidpoint (f (k:ZMod K)))/(K:ℝ))) := by
  let j : ZMod K := (k:ZMod K)
  obtain ⟨z,hz⟩ := phase_lift_exists (K:=K) k
  let c := paperAtomCenter f j+(z:ℝ)
  have hKN : 0<K := by omega
  have hKr : 0<(K:ℝ) := by exact_mod_cast hKN
  have hK2 : (2:ℝ) ≤ K := by exact_mod_cast hK
  have hzR : (k:ℝ) = (j.val:ℝ)+(K:ℝ)*z := by exact_mod_cast hz
  have hc := paper_atom_box_strict_cell hB hKN f j z hδ (y:=c) ⟨by dsimp [c]; linarith,
    by dsimp [c]; linarith⟩
  rw [←hzR] at hc
  have ce : atomBoxSum f δ y = boxWindowDensity δ (y-c) := by
    unfold atomBoxSum
    rw [Finset.sum_eq_single j]
    · have hw : -(1/2:ℝ)≤y-c ∧ y-c<1/2 := by
        have hky1 := (div_le_iff₀ hKr).mp hy.1
        have hky2 := (le_div_iff₀ hKr).mp hy.2
        have hd1 : -(1/(K:ℝ)) < y-c := by rw [← neg_div]; apply (div_lt_iff₀ hKr).2; linarith [hc.2]
        have hd2 : y-c < 1/(K:ℝ) := by apply (lt_div_iff₀ hKr).2; linarith [hc.1]
        have hz1 : (1:ℝ)/K ≤ 1/2 := by apply (div_le_iff₀ hKr).2; linarith
        exact ⟨by linarith,by linarith⟩
      unfold periodicBoxDensity
      rw [show y-paperAtomCenter f j=(y-c)+(z:ℝ) by dsimp [c]; ring,
        centeredPeriodRep_int,centeredPeriodRep_eq hw]
    · intro j' _ hj'
      by_contra hn
      exact hj' (only_own_site_in_cell hB hKN f hδ k hy j' hn)
    · simp
  have e : c=((k:ℝ)+labelCellMidpoint (f (k:ZMod K)))/(K:ℝ) := by
    unfold c paperAtomCenter labelCellMidpoint
    rw [hzR]
    change (((j.val:ℝ)+((f j).val+1/2)/(B:ℝ))/(K:ℝ))+(z:ℝ)=_
    dsimp only [j]
    field_simp
    ring
  rw [ce,e]

theorem actualSmoothedPrimitive_cell_prefix {B K : ℕ} [NeZero K]
    (hB : 0<B) (hK : 2≤K) (f : ZMod K → Fin B) {δ r : ℝ}
    (hδ0 : 0<δ) (hδ : δ<1/((B:ℝ)*K)) (k : ℤ) (hr : r∈Icc (0:ℝ) 1) :
    actualAtomicPrimitive f δ (((k:ℝ)+r)/(K:ℝ)) =
      (∫ y in ((k:ℝ)/(K:ℝ))..(((k:ℝ)+r)/(K:ℝ)),
        boxWindowDensity δ (y-(((k:ℝ)+labelCellMidpoint (f (k:ZMod K)))/(K:ℝ)))) - r := by
  let g := (k:ℝ)/(K:ℝ)
  let x := ((k:ℝ)+r)/(K:ℝ)
  let c := ((k:ℝ)+labelCellMidpoint (f (k:ZMod K)))/(K:ℝ)
  have hk : 0<(K:ℝ) := by exact_mod_cast (show 0<K by omega)
  have hx : g≤x := div_le_div_of_nonneg_right (by linarith [hr.1]) hk.le
  have e := intervalIntegral.integral_add_adjacent_intervals
    (atomBoxSum_intervalIntegrable f hδ0 0 g) (atomBoxSum_intervalIntegrable f hδ0 g x)
  have h0 := atomBoxSum_grid_primitive hB hK f hδ0 hδ k
  change (∫ y in (0:ℝ)..g,atomBoxSum f δ y)=(k:ℝ) at h0
  rw [h0] at e
  unfold actualAtomicPrimitive
  change (∫ y in (0:ℝ)..x,atomBoxSum f δ y)-(K:ℝ)*x =
    (∫ y in g..x,boxWindowDensity δ (y-c))-r
  rw [←e]
  have he : (∫ y in g..x,atomBoxSum f δ y) = ∫ y in g..x,boxWindowDensity δ (y-c) := by
    apply intervalIntegral.integral_congr
    intro y hy
    rw [uIcc_of_le hx] at hy
    exact actualBoxSum_eq_ownBox_on_cell hB hK f hδ0 hδ k y
      ⟨hy.1,hy.2.trans (div_le_div_of_nonneg_right (by linarith [hr.2]) hk.le)⟩
  rw [he]
  have er : (K:ℝ)*x=(k:ℝ)+r := by dsimp [x]; field_simp
  rw [er]
  ring

#print axioms actualSmoothedPrimitive_cell_prefix
end CenteredCubeSqrt
