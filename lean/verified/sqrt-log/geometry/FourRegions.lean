import PairBudgets
import Mathlib.Algebra.BigOperators.Fin

namespace CenteredCube.RudinDensity

open Finset

noncomputable def lagBand (a u : ℝ) (m : ℕ) : Fin 4 :=
  if (m:ℝ)*a/u ≤ 1/8 then 0
  else if (m:ℝ)*a/u ≤ 32 then 1
  else if (m:ℝ)*a/u ≤ u^3 then 2
  else 3

noncomputable def regionPairs (M : ℕ) (a u : ℝ) (r : Fin 4) : Finset (ℕ × ℕ) :=
  (forwardPairs M).filter (fun p => lagBand a u (p.2 - p.1) = r)

theorem pair_sum_eq_regions (M : ℕ) (a u : ℝ) (F : ℕ × ℕ → ℝ) :
    ∑ p ∈ forwardPairs M, F p =
      ∑ r : Fin 4, ∑ p ∈ regionPairs M a u r, F p := by
  unfold regionPairs
  exact (Finset.sum_fiberwise (forwardPairs M)
    (fun p => lagBand a u (p.2 - p.1)) F).symm

theorem region_sum_le_lags (M : ℕ) (a u : ℝ) (r : Fin 4)
    (F : ℕ × ℕ → ℝ) (G : ℕ → ℝ)
    (hG : ∀ m ∈ Ico 1 M, lagBand a u m = r → ∀ i < M - m,
      F (i, i + m) ≤ G m) :
    ∑ p ∈ regionPairs M a u r, F p ≤
      ∑ m ∈ (Ico 1 M).filter (fun m => lagBand a u m = r),
        ((M - m : ℕ) : ℝ) * G m := by
  unfold regionPairs
  rw [Finset.sum_filter]
  have hcount := sum_forwardPairs_le M
    (fun i j => if lagBand a u (j-i) = r then F (i,j) else 0)
    (fun m => if lagBand a u m = r then G m else 0) ?_
  · have H : (∑ p ∈ forwardPairs M,
        if lagBand a u (p.2-p.1) = r then F p else 0) ≤
        ∑ m ∈ Ico 1 M, if lagBand a u m = r then ((M-m:ℕ):ℝ) * G m else 0 := by
      convert hcount using 1
      refine Finset.sum_congr rfl fun m _ => ?_
      split <;> simp_all
    rw [Finset.sum_filter]
    exact H
  · intro m hm i hi
    rw [Nat.add_sub_cancel_left]
    by_cases h : lagBand a u m = r
    · simpa only [if_pos h] using hG m hm h i hi
    · simp [h]

theorem four_region_sum_le_half (M : ℕ) (a u S : ℝ) (F : ℕ × ℕ → ℝ)
    (h₀ : (∑ p ∈ regionPairs M a u 0, F p) ≤ S/4)
    (h₁ : (∑ p ∈ regionPairs M a u 1, F p) ≤ S/12)
    (h₂ : (∑ p ∈ regionPairs M a u 2, F p) ≤ S/12)
    (h₃ : (∑ p ∈ regionPairs M a u 3, F p) ≤ S/12) :
    ∑ p ∈ forwardPairs M, F p ≤ S/2 := by
  rw [pair_sum_eq_regions M a u F]
  simp only [Fin.sum_univ_four]
  exact four_region_budget h₀ h₁ h₂ h₃

end CenteredCube.RudinDensity

#print axioms CenteredCube.RudinDensity.region_sum_le_lags
#print axioms CenteredCube.RudinDensity.four_region_sum_le_half
