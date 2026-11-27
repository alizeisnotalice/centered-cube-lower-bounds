import SqrtPeriodicBoxDensity
import Mathlib.Data.ZMod.Basic

namespace CenteredCubeSqrt

open MeasureTheory Set
open scoped BigOperators Interval
open Classical

/-- True atomic box density before the 1/K normalization. -/
noncomputable def atomBoxSum {B K : ℕ} [NeZero K] (f : ZMod K → Fin B) (delta x : ℝ) : ℝ :=
  ∑ j : ZMod K, periodicBoxDensity delta (paperAtomCenter f j) x

theorem atomBoxSum_nonneg {B K : ℕ} [NeZero K] (f : ZMod K → Fin B) {delta : ℝ}
    (hδ : 0 < delta) (x : ℝ) : 0 ≤ atomBoxSum f delta x := by
  unfold atomBoxSum
  apply Finset.sum_nonneg
  intro j _
  unfold periodicBoxDensity boxWindowDensity
  exact Set.indicator_nonneg (fun _ _ => by positivity) _

theorem atomBoxSum_intervalIntegrable {B K : ℕ} [NeZero K] (f : ZMod K → Fin B)
    {delta : ℝ} (hδ : 0 < delta) (a b : ℝ) :
    IntervalIntegrable (atomBoxSum f delta) volume a b := by
  have e : atomBoxSum f delta =
      (∑ j : ZMod K, periodicBoxDensity delta (paperAtomCenter f j)) := by
    funext x
    simp only [atomBoxSum,Finset.sum_apply]
  rw [e]
  exact IntervalIntegrable.sum Finset.univ (fun (j:ZMod K) _ =>
    periodicBoxDensity_intervalIntegrable delta (paperAtomCenter f j) a b hδ)

theorem boxWindowDensity_integral_one {delta : ℝ} (hδ : 0 < delta) :
    (∫ x, boxWindowDensity delta x)=1 := by
  unfold boxWindowDensity
  rw [integral_indicator_const _ measurableSet_Icc,
    Real.volume_real_Icc_of_le (show -delta/2 ≤ delta/2 by linarith),smul_eq_mul]
  field_simp
  ring

/-- Exact strict containment of an atom box in its source coarse cell,
including the adjacent-period lifts. -/
theorem paper_atom_box_strict_cell {B K : ℕ} (hB : 0 < B) (hK : 0 < K)
    (f : ZMod K → Fin B) (j : ZMod K) (z : ℤ) {delta y : ℝ}
    (hδ : delta < 1/((B:ℝ)*K))
    (hy : -(delta/2) ≤ y-(paperAtomCenter f j+(z:ℝ)) ∧
        y-(paperAtomCenter f j+(z:ℝ)) ≤ delta/2) :
    (j.val:ℝ)+(K:ℝ)*z < (K:ℝ)*y ∧ (K:ℝ)*y < (j.val:ℝ)+(K:ℝ)*z+1 := by
  have hBr : 0 < (B:ℝ) := by exact_mod_cast hB
  have hKr : 0 < (K:ℝ) := by exact_mod_cast hK
  have hδ' : (K:ℝ)*(delta/2) < 1/(2*(B:ℝ)) := by
    have hs := mul_lt_mul_of_pos_left hδ (show 0 < (K:ℝ)/2 by positivity)
    have he : (K:ℝ)/2*(1/((B:ℝ)*K)) = 1/(2*(B:ℝ)) := by field_simp
    rw [he] at hs
    convert hs using 1; ring
  have hval : ((f j).val:ℝ)+1 ≤ B := by
    exact_mod_cast (show (f j).val+1 ≤ B from (f j).isLt)
  have huL : 1/(2*(B:ℝ)) ≤ ((f j).val+1/2)/(B:ℝ) := by
    have hw : (1:ℝ)/(2*(B:ℝ)) = (1/2)/(B:ℝ) := by field_simp
    rw [hw]
    exact div_le_div_of_nonneg_right (by linarith [show 0 ≤ ((f j).val:ℝ) by positivity] : (1/2:ℝ) ≤ (f j).val+1/2) hBr.le
  have huR : ((f j).val+1/2)/(B:ℝ)+1/(2*(B:ℝ)) ≤ 1 := by
    have hw : (1:ℝ)/(2*(B:ℝ)) = (1/2)/(B:ℝ) := by field_simp
    rw [hw,← add_div]
    apply (div_le_one hBr).2
    linarith
  have hcenter : (K:ℝ)*(paperAtomCenter f j+(z:ℝ)) =
      (j.val:ℝ)+(K:ℝ)*z+((f j).val+1/2)/(B:ℝ) := by
    unfold paperAtomCenter
    field_simp
    ring
  have lb := mul_le_mul_of_nonneg_left hy.1 hKr.le
  have ub := mul_le_mul_of_nonneg_left hy.2 hKr.le
  rw [mul_sub,hcenter] at lb ub
  exact ⟨by linarith,by linarith⟩

theorem phase_lift_exists {K : ℕ} [NeZero K] (k : ℤ) :
    ∃ z : ℤ, k = ((k:ZMod K).val:ℤ)+(K:ℤ)*z := by
  have h : (((k:ZMod K).val:ℤ):ZMod K) = (k:ZMod K) := by
    rw [Int.cast_natCast,ZMod.natCast_zmod_val]
  obtain ⟨z,hz⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp h
  exact ⟨z,by omega⟩

theorem only_own_site_in_cell {B K : ℕ} [NeZero K] (hB : 0 < B) (hK : 0 < K)
    (f : ZMod K → Fin B) {delta : ℝ}
    (hδ : delta < 1/((B:ℝ)*K)) (k : ℤ) {y : ℝ}
    (hy : y ∈ Icc ((k:ℝ)/K) (((k:ℝ)+1)/K)) (j : ZMod K)
    (h : periodicBoxDensity delta (paperAtomCenter f j) y ≠ 0) :
    j=(k:ZMod K) := by
  have hKr : 0 < (K:ℝ) := by exact_mod_cast hK
  let z := ⌊y-paperAtomCenter f j+1/2⌋
  have hs : centeredPeriodRep (y-paperAtomCenter f j) ∈ Icc (-delta/2) (delta/2) := by
    by_contra hn
    apply h
    unfold periodicBoxDensity boxWindowDensity
    exact Set.indicator_of_notMem hn _
  have hs' : -(delta/2) ≤ y-(paperAtomCenter f j+(z:ℝ)) ∧
      y-(paperAtomCenter f j+(z:ℝ)) ≤ delta/2 := by
    rcases hs with ⟨lo,hi⟩
    unfold centeredPeriodRep at lo hi
    dsimp [z]
    exact ⟨by linarith,by linarith⟩
  have hj := paper_atom_box_strict_cell hB hK f j z hδ hs'
  have hky : (k:ℝ) ≤ (K:ℝ)*y ∧ (K:ℝ)*y ≤ (k:ℝ)+1 := by
    exact ⟨by rw [mul_comm]; exact (div_le_iff₀ hKr).mp hy.1,
      by rw [mul_comm]; exact (le_div_iff₀ hKr).mp hy.2⟩
  let jz : ℤ := (j.val:ℤ)+(K:ℤ)*z
  have hjz1 : (jz:ℝ) < (k:ℝ)+1 := by
    dsimp [jz]; push_cast
    linarith [hj.1,hky.2]
  have hjz2 : (k:ℝ) < (jz:ℝ)+1 := by
    dsimp [jz]; push_cast
    linarith [hj.2,hky.1]
  have e : jz=k := by
    have h1 : jz < k+1 := by exact_mod_cast hjz1
    have h2 : k < jz+1 := by exact_mod_cast hjz2
    omega
  have ec := congrArg (fun m : ℤ => (m:ZMod K)) e
  simpa [jz,Int.cast_add,Int.cast_mul,Int.cast_natCast] using ec

/-- Each coarse cell carries exactly one unit of actual box mass. -/
theorem atomBoxSum_cell_mass {B K : ℕ} [NeZero K] (hB : 0 < B) (hK : 2 ≤ K)
    (f : ZMod K → Fin B) {delta : ℝ}
    (hδ0 : 0 < delta) (hδ : delta < 1/((B:ℝ)*K)) (k : ℤ) :
    (∫ y in (k:ℝ)/K..((k:ℝ)+1)/K, atomBoxSum f delta y) = 1 := by
  let j : ZMod K := (k:ZMod K)
  obtain ⟨z,hz⟩ := phase_lift_exists (K:=K) k
  let c := paperAtomCenter f j+(z:ℝ)
  have hKN : 0<K := by omega
  have hKr : 0<(K:ℝ) := by exact_mod_cast hKN
  have hK2 : (2:ℝ) ≤ K := by exact_mod_cast hK
  have hzR : (k:ℝ) = (j.val:ℝ)+(K:ℝ)*z := by exact_mod_cast hz
  have hc := paper_atom_box_strict_cell hB hKN f j z hδ (y:=c) ⟨by dsimp [c]; linarith,
    by dsimp [c]; linarith⟩
  rw [← hzR] at hc
  have ce (y : ℝ) (hy : y ∈ Icc ((k:ℝ)/K) (((k:ℝ)+1)/K)) :
      atomBoxSum f delta y = boxWindowDensity delta (y-c) := by
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
  have hends : (k:ℝ)/K ≤ ((k:ℝ)+1)/K := div_le_div_of_nonneg_right (by linarith) hKr.le
  rw [intervalIntegral.integral_congr (fun y hy => ce y (by rwa [uIcc_of_le hends] at hy))]
  rw [intervalIntegral.integral_eq_integral_of_support_subset]
  · rw [integral_sub_right_eq_self,boxWindowDensity_integral_one hδ0]
  · intro y hy
    have hb' : y-c ∈ Icc (-delta/2) (delta/2) := by
      by_contra h
      exact hy (Set.indicator_of_notMem h _)
    have hbox := paper_atom_box_strict_cell hB hKN f j z hδ (y:=y)
      ⟨by linarith [hb'.1],hb'.2⟩
    rw [← hzR] at hbox
    exact ⟨(div_lt_iff₀ hKr).2 (by linarith [hbox.1]),
      (le_div_iff₀ hKr).2 (by linarith [hbox.2])⟩

#print axioms paper_atom_box_strict_cell
#print axioms only_own_site_in_cell
#print axioms atomBoxSum_cell_mass

end CenteredCubeSqrt
