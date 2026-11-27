import SqrtPhysicalCounting
import Mathlib.Data.Finset.Filter

namespace CenteredCubeSqrt

open scoped BigOperators
open Classical

variable {G : Type*} [AddGroup G] [Fintype G]

noncomputable def ordinalPairFiber {B : ℕ} (f : G → Fin B) (k : G) (y z : ℕ) : Finset G :=
  Finset.univ.filter fun j => (f j).val=y ∧ (f (j+k)).val=z

noncomputable def ordinalLagHits {B : ℕ} (f : G → Fin B) (k : G) (r : ℤ) : Finset G :=
  Finset.univ.filter fun j => (↑(f (j+k)).val : ℤ) - ↑(f j).val = r

theorem lower_ordinal_lag_count {B b : ℕ} (hb : b < B)
    (f : G → Fin B) (k : G) :
    (ordinalLagHits f k (b:ℤ)).card =
      ∑ y ∈ Finset.range (B-b), (ordinalPairFiber f k y (y+b)).card := by
  calc
    _ = ∑ y ∈ Finset.range (B-b), ((ordinalLagHits f k (b:ℤ)).filter fun j => (f j).val=y).card := by
      apply Finset.card_eq_sum_card_fiberwise
      intro j hj
      have h := (Finset.mem_filter.mp hj).2
      have h1 := (f j).isLt
      have h2 := (f (j+k)).isLt
      apply Finset.mem_range.mpr
      change (f j).val < B-b
      omega
    _ = _ := by
      apply Finset.sum_congr rfl
      intro y hy
      congr 1
      ext j
      simp only [ordinalLagHits,ordinalPairFiber,Finset.mem_filter,Finset.mem_univ,true_and]
      constructor
      · rintro ⟨h,hy'⟩
        exact ⟨hy',by omega⟩
      · rintro ⟨h1,h2⟩
        exact ⟨by omega,h1⟩

theorem upper_ordinal_lag_count {B b : ℕ} (hb : b < B)
    (f : G → Fin B) (k : G) :
    (ordinalLagHits f k ((b:ℤ)-B)).card =
      ∑ z ∈ Finset.range b, (ordinalPairFiber f k (z+B-b) z).card := by
  calc
    _ = ∑ z ∈ Finset.range b, ((ordinalLagHits f k ((b:ℤ)-B)).filter fun j => (f (j+k)).val=z).card := by
      apply Finset.card_eq_sum_card_fiberwise
      intro j hj
      have h := (Finset.mem_filter.mp hj).2
      have h1 := (f j).isLt
      have h2 := (f (j+k)).isLt
      apply Finset.mem_range.mpr
      change (f (j+k)).val < b
      omega
    _ = _ := by
      apply Finset.sum_congr rfl
      intro z hz
      congr 1
      ext j
      simp only [ordinalLagHits,ordinalPairFiber,Finset.mem_filter,Finset.mem_univ,true_and]
      constructor
      · rintro ⟨h,hz'⟩
        exact ⟨by omega,hz'⟩
      · rintro ⟨h1,h2⟩
        exact ⟨by omega,h2⟩

/-- Combining the two integer carry fibers and taking the exact regular
nonzero-state law as input adds precisely the q/B−indicator count. -/
theorem two_regular_ordinal_lag_count {q B b A : ℕ} (hb : b < B) (hA : q=B*B*A)
    (hp : 0 < A) (f : G → Fin B) (k l : G)
    (h0 : ∀ y z : ℕ, y<B → z<B →
      (ordinalPairFiber f k y z).card = A - if y=0 ∧ z=0 then 1 else 0)
    (h1 : ∀ y z : ℕ, y<B → z<B →
      (ordinalPairFiber f l y z).card = A - if y=0 ∧ z=0 then 1 else 0) :
    (ordinalLagHits f k b).card + (ordinalLagHits f l ((b:ℤ)-B)).card =
      q/B - if b=0 then 1 else 0 := by
  rw [lower_ordinal_lag_count hb, upper_ordinal_lag_count hb]
  apply physical_count_from_regular_fibers hb hA _ _ _ _ hp
  · intro y hy
    have hy' := Finset.mem_range.mp hy
    rw [h0 y (y+b) (by omega) (by omega)]
    simp
  · intro z hz
    have hz' := Finset.mem_range.mp hz
    have hfalse : ¬ (z+B-b=0 ∧ z=0) := by omega
    rw [h1 (z+B-b) z (by omega) (by omega),ite_eq_right hfalse,Nat.sub_zero]

#print axioms lower_ordinal_lag_count
#print axioms upper_ordinal_lag_count
#print axioms two_regular_ordinal_lag_count

end CenteredCubeSqrt
