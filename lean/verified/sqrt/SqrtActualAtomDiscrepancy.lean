import SqrtAtomCellMass
import SqrtActualAtomicIncrement

namespace CenteredCubeSqrt

open MeasureTheory
open scoped BigOperators Interval

noncomputable def actualAtomicPrimitive {B K : ℕ} [NeZero K] (f : ZMod K → Fin B)
    (delta x : ℝ) : ℝ :=
  (∫ y in (0:ℝ)..x, atomBoxSum f delta y)-(K:ℝ)*x

theorem atomBoxSum_grid_primitive {B K : ℕ} [NeZero K] (hB : 0 < B) (hK : 2 ≤ K)
    (f : ZMod K → Fin B) {delta : ℝ}
    (hδ0 : 0 < delta) (hδ : delta < 1/((B:ℝ)*K)) (k : ℤ) :
    (∫ y in (0:ℝ)..(k:ℝ)/K, atomBoxSum f delta y) = k := by
  let c (k : ℤ) : ℝ := (k:ℝ)/K
  let F := atomBoxSum f delta
  have steps (i : ℤ) : (∫ y in (0:ℝ)..c (i+1), F y) = (∫ y in (0:ℝ)..c i,F y)+1 := by
    have h := intervalIntegral.integral_add_adjacent_intervals
      (atomBoxSum_intervalIntegrable f hδ0 0 (c i))
      (atomBoxSum_intervalIntegrable f hδ0 (c i) (c (i+1)))
    have e := atomBoxSum_cell_mass hB hK f hδ0 hδ i
    have er : c (i+1)=((i:ℝ)+1)/K := by simp [c,Int.cast_add]
    rw [er, e] at h
    rw [er]
    exact h.symm
  change (∫ y in (0:ℝ)..c k,F y) = k
  induction k using Int.induction_on with
  | zero => simp [c]
  | succ i ih =>
    rw [steps,ih,Int.cast_add,Int.cast_one]
  | pred i ih =>
    have h := steps (-(i:ℤ)-1)
    rw [sub_add_cancel,ih] at h
    push_cast at h ⊢
    linarith

/-- The primitive of the actual box density minus K is bounded by one,
uniformly on the full line, not just sampled points or a label average. -/
theorem actualAtomicPrimitive_abs_le_one {B K : ℕ} [NeZero K] (hB : 0 < B) (hK : 2 ≤ K)
    (f : ZMod K → Fin B) {delta : ℝ}
    (hδ0 : 0 < delta) (hδ : delta < 1/((B:ℝ)*K)) (x : ℝ) :
    |actualAtomicPrimitive f delta x| ≤ 1 := by
  let F := atomBoxSum f delta
  let k := ⌊(K:ℝ)*x⌋
  let l : ℝ := (k:ℝ)/K
  let u : ℝ := ((k:ℝ)+1)/K
  have hKp : 0 < (K:ℝ) := by exact_mod_cast (show 0<K by omega)
  have hfloor : (k:ℝ) ≤ (K:ℝ)*x := Int.floor_le _
  have hceil : (K:ℝ)*x < (k:ℝ)+1 := Int.lt_floor_add_one _
  have hl : l ≤ x := (div_le_iff₀ hKp).mpr (by linarith)
  have hu : x ≤ u := (le_div_iff₀ hKp).mpr (by linarith)
  have base : (∫ y in (0:ℝ)..l,F y) = k := atomBoxSum_grid_primitive hB hK f hδ0 hδ k
  have total : (∫ y in l..u,F y) = 1 := atomBoxSum_cell_mass hB hK f hδ0 hδ k
  have adj := intervalIntegral.integral_add_adjacent_intervals
    (atomBoxSum_intervalIntegrable f hδ0 l x) (atomBoxSum_intervalIntegrable f hδ0 x u)
  have adj0 := intervalIntegral.integral_add_adjacent_intervals
    (atomBoxSum_intervalIntegrable f hδ0 0 l) (atomBoxSum_intervalIntegrable f hδ0 l x)
  have hnonneg := intervalIntegral.integral_nonneg_of_forall (μ:=volume) hl (atomBoxSum_nonneg f hδ0)
  have hnonneg' := intervalIntegral.integral_nonneg_of_forall (μ:=volume) hu (atomBoxSum_nonneg f hδ0)
  change |(∫ y in 0..x,F y)-(K:ℝ)*x|≤1
  rw [← adj0,base]
  rw [total] at adj
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem actualAtomicWindow_eq_primitive {B K : ℕ} [NeZero K] (f : ZMod K → Fin B)
    {delta L : ℝ} (hδ : 0<delta) (x : ℝ) :
    actualAtomicWindow f delta L x =
      actualAtomicPrimitive f delta (x+L/2)-actualAtomicPrimitive f delta (x-L/2) := by
  let l := x-L/2
  let u := x+L/2
  let F := atomBoxSum f delta
  have e : (∫ y in l..u,F y) =
      ∑ j : ZMod K, ∫ y in l..u, periodicBoxDensity delta (paperAtomCenter f j) y := by
    unfold F atomBoxSum
    rw [intervalIntegral.integral_finsetSum]
    intro j _
    exact periodicBoxDensity_intervalIntegrable delta (paperAtomCenter f j) l u hδ
  have adj := intervalIntegral.integral_add_adjacent_intervals
    (atomBoxSum_intervalIntegrable f hδ 0 l) (atomBoxSum_intervalIntegrable f hδ l u)
  unfold actualAtomicWindow actualAtomicPrimitive
  change (∑ j : ZMod K, ∫ y in l..u, periodicBoxDensity delta (paperAtomCenter f j) y) -
    (K:ℝ)*L = ((∫ y in 0..u,F y)-(K:ℝ)*u)-((∫ y in 0..l,F y)-(K:ℝ)*l)
  rw [← e]
  dsimp [l,u]
  linarith

/-- Actual centered atom-window discrepancy is uniformly at most two. -/
theorem actualAtomicWindow_abs_le_two {B K : ℕ} [NeZero K] (hB : 0<B) (hK : 2≤K)
    (f : ZMod K → Fin B) {delta L : ℝ} (hδ0 : 0<delta)
    (hδ : delta < 1/((B:ℝ)*K)) (x : ℝ) :
    |actualAtomicWindow f delta L x| ≤ 2 := by
  rw [actualAtomicWindow_eq_primitive f hδ0]
  exact (abs_sub _ _).trans (by
    linarith [actualAtomicPrimitive_abs_le_one hB hK f hδ0 hδ (x+L/2),
      actualAtomicPrimitive_abs_le_one hB hK f hδ0 hδ (x-L/2)])

theorem actualAtomicWindow_continuous {B K : ℕ} [NeZero K]
    (f : ZMod K → Fin B) {delta : ℝ} (hδ0 : 0<delta) (L : ℝ) :
    Continuous (actualAtomicWindow f delta L) := by
  have hf := intervalIntegral.continuous_primitive (atomBoxSum_intervalIntegrable f hδ0) 0
  have hP : Continuous (actualAtomicPrimitive f delta) :=
    hf.sub (continuous_const.mul continuous_id)
  have e : actualAtomicWindow f delta L =
      fun x => actualAtomicPrimitive f delta (x+L/2)-actualAtomicPrimitive f delta (x-L/2) :=
    funext (actualAtomicWindow_eq_primitive f hδ0)
  rw [e]
  exact (hP.comp (continuous_id.add continuous_const)).sub
    (hP.comp (continuous_id.sub continuous_const))

#print axioms actualAtomicPrimitive_abs_le_one
#print axioms actualAtomicWindow_abs_le_two
#print axioms actualAtomicWindow_continuous

end CenteredCubeSqrt
