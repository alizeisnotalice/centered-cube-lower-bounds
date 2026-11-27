import SqrtRawCellEnergy
import SqrtAtomResidue
import Mathlib.MeasureTheory.Function.Floor

namespace CenteredCubeSqrt
open MeasureTheory Set
open scoped Interval BigOperators
set_option maxHeartbeats 1400000

noncomputable def actualRawPrimitive {B K : ℕ} [NeZero K] (f : ZMod K → Fin B) (x : ℝ) : ℝ :=
  let j := ⌊(K:ℝ)*x⌋
  cellPrimitive (labelCellMidpoint (f (j:ZMod K))) ((K:ℝ)*x-(j:ℝ))

noncomputable def actualRawWindow {B K : ℕ} [NeZero K] (f : ZMod K → Fin B) (L x : ℝ) :=
  actualRawPrimitive f (x+L/2)-actualRawPrimitive f (x-L/2)

theorem actualRawPrimitive_periodic {B K : ℕ} [NeZero K] (f : ZMod K → Fin B) :
    Function.Periodic (actualRawPrimitive f) 1 := by
  intro x
  unfold actualRawPrimitive
  rw [show (K:ℝ)*(x+1)=(K:ℝ)*x+((K:ℤ):ℝ) by push_cast; ring,
    Int.floor_add_intCast]
  dsimp only
  simp only [Int.cast_add]
  have h1 : (⌊(K:ℝ)*x⌋:ZMod K)+((K:ℤ):ZMod K)=(⌊(K:ℝ)*x⌋:ZMod K) := by
    push_cast
    simp
  rw [h1]
  have he : (K:ℝ)*x+((K:ℤ):ℝ)-(((⌊(K:ℝ)*x⌋:ℤ):ℝ)+((K:ℤ):ℝ))=(K:ℝ)*x-((⌊(K:ℝ)*x⌋:ℤ):ℝ) := by ring
  rw [he]

theorem actualRawPrimitive_in_cell {B K : ℕ} [NeZero K] (f : ZMod K → Fin B)
    (j : ℤ) {r : ℝ} (hr : r∈Ico (0:ℝ) 1) :
    actualRawPrimitive f (((j:ℝ)+r)/(K:ℝ)) =
      cellPrimitive (labelCellMidpoint (f (j:ZMod K))) r := by
  have hK : (K:ℝ)≠0 := by exact_mod_cast (NeZero.ne K)
  have he : (K:ℝ)*(((j:ℝ)+r)/(K:ℝ))=(j:ℝ)+r := by field_simp
  have hf : ⌊(j:ℝ)+r⌋=j := Int.floor_eq_iff.mpr ⟨by linarith [hr.1],by linarith [hr.2]⟩
  unfold actualRawPrimitive
  rw [he,hf]
  have er : (j:ℝ)+r-(j:ℝ)=r := by ring
  dsimp only
  rw [er]

theorem cellPrimitive_abs_le_one {u r : ℝ} (hr : r∈Icc (0:ℝ) 1) :
    |cellPrimitive u r|≤1 := by
  unfold cellPrimitive
  split
  · rw [abs_of_nonneg (by linarith [hr.2])]
    linarith [hr.1]
  · rw [zero_sub,abs_neg,abs_of_nonneg hr.1]
    exact hr.2

theorem actualRawPrimitive_abs_le_one {B K : ℕ} [NeZero K] (f : ZMod K → Fin B) (x : ℝ) :
    |actualRawPrimitive f x|≤1 := by
  apply cellPrimitive_abs_le_one
  exact ⟨by linarith [Int.floor_le ((K:ℝ)*x)],by linarith [Int.lt_floor_add_one ((K:ℝ)*x)]⟩

theorem actualRawPrimitive_measurable {B K : ℕ} [NeZero K] (f : ZMod K → Fin B) :
    Measurable (actualRawPrimitive f) := by
  let J (x : ℝ) := ⌊(K:ℝ)*x⌋
  let R (x : ℝ) := (K:ℝ)*x-(J x:ℝ)
  let U (x : ℝ) := labelCellMidpoint (f (J x:ZMod K))
  have hj : Measurable J := Int.measurable_floor.comp (measurable_const.mul measurable_id)
  have hr : Measurable R := (measurable_const.mul measurable_id).sub ((measurable_of_countable (fun i : ℤ => (i:ℝ))).comp hj)
  have hu : Measurable U := by
    exact ((measurable_of_countable (fun i : ℤ => labelCellMidpoint (f (i:ZMod K)))).comp hj)
  have he : MeasurableSet {x | U x≤R x} := measurableSet_le hu hr
  change Measurable (fun x => (if U x≤R x then (1:ℝ) else 0)-R x)
  exact (Measurable.ite he measurable_const measurable_const).sub hr

theorem actualRawPrimitive_intervalIntegrable {B K : ℕ} [NeZero K] (f : ZMod K → Fin B)
    (a b : ℝ) :
    IntervalIntegrable (actualRawPrimitive f) volume a b := by
  rw [intervalIntegrable_iff]
  apply Measure.integrableOn_of_bounded (M:=1) (s_finite:=by rw [uIoc]; simp [Real.volume_Ioc])
    (actualRawPrimitive_measurable f).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using actualRawPrimitive_abs_le_one f x)

#print axioms actualRawPrimitive_periodic
#print axioms actualRawPrimitive_in_cell
#print axioms actualRawPrimitive_intervalIntegrable

end CenteredCubeSqrt
