import Lean

namespace CenteredCubeSqrt

/-- Sum over labels 0 through `n-1`. -/
def sumLabels (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n+1 => sumLabels f n + f n

theorem sumLabels_const {f : Nat → Nat} {n A : Nat} (h : ∀ y < n, f y = A) :
    sumLabels f n = n*A := by
  induction n with
  | zero => simp [sumLabels]
  | succ n ih =>
    rw [sumLabels, ih (fun y hy => h y (by omega)), h n (by omega), Nat.succ_mul]

theorem sumLabels_zero_corrected {f : Nat → Nat} {n A : Nat}
    (hn : 0 < n) (hA : 0 < A) (h : ∀ y < n, f y = A - if y = 0 then 1 else 0) :
    sumLabels f n = n*A-1 := by
  induction n with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero =>
      simp only [sumLabels, Nat.zero_add, Nat.one_mul]
      exact h 0 (by omega)
    | succ n =>
      have h0 : sumLabels f (n+1) = (n+1)*A-1 :=
        ih (by omega) (fun y hy => h y (by omega))
      have h1 : f (n+1) = A := by simpa using h (n+1) (by omega)
      rw [sumLabels, h0, h1, Nat.succ_mul (n+1) A]
      have hA' : 1 ≤ (n+1)*A := by rw [Nat.succ_mul]; omega
      omega

/-- Exact count when both coarse carry classes are regular: only the zero
label pair loses one nonzero state. The constant `A` is q/B². -/
theorem regular_physical_count_core {q B b A : Nat}
    (hb : b < B) (hA : q = B*B*A) (hp : 0 < A)
    (N0 N1 : Nat → Nat)
    (h0 : ∀ y < B-b, N0 y = A - if y = 0 ∧ b = 0 then 1 else 0)
    (h1 : ∀ y < b, N1 y = A) :
    sumLabels N0 (B-b) + sumLabels N1 b = q/B - if b=0 then 1 else 0 := by
  have hd : q/B = B*A := by
    rw [hA, Nat.mul_assoc, Nat.mul_div_cancel_left _ (by omega)]
  rw [hd, sumLabels_const h1]
  by_cases hh : b = 0
  · subst b
    simp only [Nat.sub_zero, Nat.zero_mul, Nat.add_zero, and_true] at h0 ⊢
    exact sumLabels_zero_corrected (by omega) hp h0
  · simp only [hh, and_false, ite_false, Nat.sub_zero] at h0 ⊢
    rw [sumLabels_const h0, ← Nat.add_mul]
    have : B-b+b = B := by omega
    rw [this]

/-- A strictly positive difference below one coarse cell uses only the
upper carry, and each of its `b` label pairs realizes q/B² states. -/
theorem small_positive_physical_count_core {b A : Nat} (N : Nat → Nat)
    (h : ∀ y < b, N y = A) : sumLabels N b = b*A := sumLabels_const h

#print axioms regular_physical_count_core
#print axioms small_positive_physical_count_core

end CenteredCubeSqrt
