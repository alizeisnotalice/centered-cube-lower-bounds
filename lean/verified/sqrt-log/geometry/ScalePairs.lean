import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

open Finset
namespace CenteredCube.RudinDensity

def forwardPairs (M : ℕ) : Finset (ℕ × ℕ) :=
  ((range M) ×ˢ (range M)).filter (fun p => p.1 < p.2)

def lagPairs (M : ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  (Ico 1 M).sigma (fun m => range (M - m))

def lagToPair (p : Σ _ : ℕ, ℕ) : ℕ × ℕ :=
  (p.2, p.2 + p.1)

theorem lagToPair_injective : Function.Injective lagToPair := by
  rintro ⟨m, i⟩ ⟨m', i'⟩ h
  change (i, i + m) = (i', i' + m') at h
  have hi : i = i' := congrArg Prod.fst h
  have hm : i + m = i' + m' := congrArg Prod.snd h
  have hl : m = m' := by omega
  subst m'
  subst i'
  rfl

theorem lagPairs_image (M : ℕ) : (lagPairs M).image lagToPair = forwardPairs M := by
  ext p
  rcases p with ⟨i, j⟩
  simp only [mem_image, lagPairs, mem_sigma, mem_Ico, mem_range, forwardPairs,
    mem_filter, mem_product, lagToPair, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨m, r⟩, ⟨⟨hl, hh⟩, hri⟩, hi, hj⟩
    simp only at *
    omega
  · rintro ⟨⟨hi, hj⟩, hij⟩
    refine ⟨⟨j - i, i⟩, ⟨⟨?_, ?_⟩, ?_⟩, rfl, ?_⟩
    · change 1 ≤ j - i
      omega
    · change j - i < M
      omega
    · change i < M - (j - i)
      omega
    · change i + (j - i) = j
      omega

theorem sum_forwardPairs_eq {R : Type*} [AddCommMonoid R] (M : ℕ) (F : ℕ → ℕ → R) :
    ∑ p ∈ forwardPairs M, F p.1 p.2 =
      ∑ m ∈ Ico 1 M, ∑ i ∈ range (M - m), F i (i + m) := by
  rw [← lagPairs_image, Finset.sum_image lagToPair_injective.injOn]
  exact Finset.sum_sigma (Ico 1 M) (fun m => range (M - m))
    (fun p : Σ _ : ℕ, ℕ => F p.2 (p.2 + p.1))

theorem sum_forwardPairs_le (M : ℕ) (F : ℕ → ℕ → ℝ) (G : ℕ → ℝ)
    (h : ∀ m ∈ Ico 1 M, ∀ i < M - m, F i (i + m) ≤ G m) :
    ∑ p ∈ forwardPairs M, F p.1 p.2 ≤
      ∑ m ∈ Ico 1 M, (M - m : ℕ) * G m := by
  rw [sum_forwardPairs_eq]
  refine Finset.sum_le_sum fun m hm => ?_
  calc
    (∑ i ∈ range (M - m), F i (i + m)) ≤ ∑ _i ∈ range (M - m), G m :=
      Finset.sum_le_sum fun i hi => h m hm i (Finset.mem_range.mp hi)
    _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

theorem sum_forwardPairs_triangular {R : Type*} [AddCommMonoid R] (M : ℕ)
    (F : ℕ → ℕ → R) :
    ∑ p ∈ forwardPairs M, F p.1 p.2 =
      ∑ j ∈ range M, ∑ i ∈ range j, F i j := by
  refine Finset.sum_finset_product_right' (forwardPairs M) (range M) range ?_
  rintro ⟨i, j⟩
  simp only [forwardPairs, mem_filter, mem_product, mem_range]
  omega

theorem forwardPairs_card_bound (M : ℕ) :
    ((forwardPairs M).card : ℝ) ≤ (M : ℝ)^2 / 2 := by
  have h : (forwardPairs M).card = ∑ j ∈ range M, j := by
    simpa [Finset.sum_const] using
      (sum_forwardPairs_triangular M (fun _ _ => (1 : ℕ)))
  rw [h]
  have hmul := Finset.sum_range_id_mul_two M
  have hcast : (∑ j ∈ range M, (j : ℝ)) * 2 =
      (M : ℝ) * ((M - 1 : ℕ) : ℝ) := by
    simpa only [Nat.cast_mul, Nat.cast_sum, Nat.cast_ofNat] using
      congrArg (fun n : ℕ => (n : ℝ)) hmul
  rw [Nat.cast_sum]
  have hle : ((M - 1 : ℕ) : ℝ) ≤ (M : ℝ) := by
    exact_mod_cast (Nat.sub_le M 1)
  nlinarith only [hcast, mul_le_mul_of_nonneg_left hle (show 0 ≤ (M : ℝ) by positivity)]

end CenteredCube.RudinDensity

#print axioms CenteredCube.RudinDensity.sum_forwardPairs_eq
#print axioms CenteredCube.RudinDensity.sum_forwardPairs_le
#print axioms CenteredCube.RudinDensity.sum_forwardPairs_triangular
#print axioms CenteredCube.RudinDensity.forwardPairs_card_bound
