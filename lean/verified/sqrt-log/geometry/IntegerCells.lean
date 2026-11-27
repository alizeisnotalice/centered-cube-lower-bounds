import Cubes
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.MeasureTheory.Function.Floor

open MeasureTheory Set

namespace CenteredCube

def cellShift {n : ℕ} (k : Fin n → ℤ) : Space n := fun i => (k i:ℝ)

def unitCell (n : ℕ) : Set (Space n) := univ.pi (fun _ => Ioc (0:ℝ) 1)

def affineCell {n : ℕ} (k : Fin n → ℤ) : Set (Space n) :=
  univ.pi (fun i => Ioc (k i:ℝ) ((k i:ℝ)+1))

noncomputable def ceilIndex {n : ℕ} (x : Space n) : Fin n → ℤ :=
  fun i => ⌈x i⌉ - 1

noncomputable def cellRep {n : ℕ} (x : Space n) : Space n :=
  x - cellShift (ceilIndex x)

theorem affineCell_iff {n : ℕ} {k : Fin n → ℤ} {x : Space n} :
    x ∈ affineCell k ↔ ceilIndex x = k := by
  rw [affineCell,mem_univ_pi,funext_iff]
  apply forall_congr'
  intro i
  have h : (⌈x i⌉ - 1 : ℤ) = k i ↔ ⌈x i⌉ = k i + 1 := by omega
  simp only [ceilIndex,h,Int.ceil_eq_iff,Int.cast_add,Int.cast_one,add_sub_cancel_right,mem_Ioc]

theorem cellRep_measurable {n : ℕ} : Measurable (@cellRep n) := by
  apply measurable_pi_lambda
  intro i
  have h : Measurable (fun x : Space n => ⌈x i⌉) :=
    Int.measurable_ceil.comp (measurable_pi_apply i)
  unfold cellRep cellShift ceilIndex
  simp only [Pi.sub_apply, Int.cast_sub, Int.cast_one]
  exact (measurable_pi_apply i).sub
    (((measurable_of_countable (fun j : ℤ => (j:ℝ))).comp h).sub measurable_const)

theorem affineCell_measurable {n : ℕ} (k : Fin n → ℤ) : MeasurableSet (affineCell k) :=
  MeasurableSet.univ_pi (fun _ => measurableSet_Ioc)

theorem unitCell_measurable (n : ℕ) : MeasurableSet (unitCell n) :=
  MeasurableSet.univ_pi (fun _ => measurableSet_Ioc)

theorem cellRep_on_tile {n : ℕ} {k : Fin n → ℤ} {x : Space n} (hx : x ∈ affineCell k) :
    cellRep x = x-cellShift k := by
  unfold cellRep
  rw [affineCell_iff.mp hx]

theorem tile_shift_iff {n : ℕ} {k : Fin n → ℤ} {x : Space n} :
    x ∈ affineCell k ↔ x-cellShift k ∈ unitCell n := by
  simp only [affineCell,unitCell,mem_univ_pi,mem_Ioc,cellShift,Pi.sub_apply]
  apply forall_congr'
  intro i
  constructor <;> rintro ⟨hlo,hhi⟩ <;> constructor <;> linarith

theorem cellRep_mem {n : ℕ} (x : Space n) : cellRep x ∈ unitCell n := by
  apply (tile_shift_iff (k := ceilIndex x)).mp
  exact affineCell_iff.mpr rfl

def boxKeys (n N : ℕ) := Fin n → Fin N

def translatedKey {n N : ℕ} (L : ℤ) (k : boxKeys n N) : Fin n → ℤ :=
  fun i => L + (k i).val

theorem translatedKey_inj {n N : ℕ} (L : ℤ) : Function.Injective (@translatedKey n N L) := by
  intro k j h
  funext i
  apply Fin.ext
  have hi := congrFun h i
  unfold translatedKey at hi
  omega

def openIntBox (n : ℕ) (L : ℤ) (N : ℕ) : Set (Space n) :=
  univ.pi (fun _ => Ioc (L:ℝ) ((L:ℝ)+(N:ℝ)))

theorem openIntBox_partition (n : ℕ) (L : ℤ) (N : ℕ) :
    openIntBox n L N = ⋃ k : boxKeys n N, affineCell (translatedKey L k) := by
  ext x
  rw [mem_iUnion]
  constructor
  · intro hx
    have h (i : Fin n) := mem_univ_pi.mp hx i
    have hi (i : Fin n) : L ≤ ceilIndex x i ∧ ceilIndex x i < L + (N:ℤ) := by
      have hu := (Int.ceil_eq_iff.mp (rfl : ⌈x i⌉ = ⌈x i⌉))
      have hlo' : (L:ℝ) < (⌈x i⌉:ℝ) := (h i).1.trans_le hu.2
      have hlo : L < ⌈x i⌉ := by exact_mod_cast hlo'
      have hhi' : (⌈x i⌉:ℝ)-1 < (L:ℝ)+(N:ℝ) := hu.1.trans_le (h i).2
      have hhi'': (((⌈x i⌉-1 : ℤ):ℝ)) < (((L+(N:ℤ)):ℤ):ℝ) := by
        push_cast
        exact hhi'
      have hhi : ⌈x i⌉-1 < L+(N:ℤ) := by exact_mod_cast hhi''
      unfold ceilIndex
      omega
    let k : boxKeys n N := fun i => ⟨(ceilIndex x i-L).toNat, by have H:=hi i; omega⟩
    refine ⟨k,affineCell_iff.mpr ?_⟩
    funext i
    have H := hi i
    unfold translatedKey
    change ceilIndex x i = L + ((ceilIndex x i-L).toNat:ℤ)
    omega
  · rintro ⟨k,hk⟩
    apply mem_univ_pi.mpr
    intro i
    have H := mem_univ_pi.mp hk i
    have h0 : (0:ℝ) ≤ ((k i).val:ℝ) := by positivity
    have hN : ((k i).val+1:ℕ) ≤ N := (k i).isLt
    have hR : ((k i).val:ℝ)+1 ≤ (N:ℝ) := by exact_mod_cast hN
    change (L:ℝ) < x i ∧ x i ≤ (L:ℝ)+(N:ℝ)
    change ((translatedKey L k i:ℤ):ℝ) < x i ∧ x i ≤ ((translatedKey L k i:ℤ):ℝ)+1 at H
    simp only [translatedKey,Int.cast_add,Int.cast_natCast] at H
    exact ⟨by linarith [H.1], by linarith [H.2]⟩

theorem affineCell_pairwise {n N : ℕ} (L : ℤ) :
    Pairwise (fun k j : boxKeys n N => Disjoint (affineCell (translatedKey L k))
      (affineCell (translatedKey L j))) := by
  intro k j h
  rw [Set.disjoint_left]
  intro x hk hj
  exact h (translatedKey_inj L ((affineCell_iff.mp hk).symm.trans (affineCell_iff.mp hj)))

end CenteredCube

#print axioms CenteredCube.openIntBox_partition
#print axioms CenteredCube.cellRep_measurable
