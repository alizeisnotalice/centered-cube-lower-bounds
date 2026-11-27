import LagAssembly
import ProbabilityScores
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Order.Lattice.Nat

namespace CenteredCube.RudinDensity

open MeasureTheory Set
open Finset

theorem second_bonferroni {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (E : ℕ → Set Ω) (hE : ∀ i, MeasurableSet (E i)) (n : ℕ) :
    (∑ j ∈ range n, μ.real (E j)) -
        (∑ j ∈ range n, ∑ i ∈ range j, μ.real (E i ∩ E j))
      ≤ μ.real (⋃ j < n, E j) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, sum_range_succ, biUnion_lt_succ]
    have hu := measureReal_union_add_inter
      (μ := μ) (s := ⋃ j < n, E j) (hE n)
    have hdist : (⋃ j < n, E j) ∩ E n = ⋃ j ∈ range n, (E j ∩ E n) := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_iUnion, Finset.mem_range]
      aesop
    have hp : μ.real ((⋃ j < n, E j) ∩ E n) ≤
        ∑ i ∈ range n, μ.real (E i ∩ E n) := by
      rw [hdist]
      exact measureReal_biUnion_finset_le _ _
    linarith only [ih, hu, hp]

theorem half_marginal_halo_mass {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (E : ℕ → Set Ω)
    (hE : ∀ i, MeasurableSet (E i)) (M : ℕ) (p : ℝ)
    (hMarginal : ∀ i < M, p ≤ μ.real (E i))
    (hBudget : (∑ q ∈ forwardPairs M, μ.real (E q.1 ∩ E q.2)) ≤
      (∑ j ∈ range M, μ.real (E j))/2) :
    (M:ℝ)*p/2 ≤ μ.real (⋃ j < M, E j) := by
  have h := second_bonferroni μ E hE M
  have H : (M:ℝ)*p ≤ ∑ j ∈ range M, μ.real (E j) := by
    simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using
      (Finset.sum_le_sum fun j hj => hMarginal j (mem_range.mp hj) :
        (∑ _j ∈ range M, p) ≤ ∑ j ∈ range M, μ.real (E j))
  rw [sum_forwardPairs_triangular M (fun i j => μ.real (E i ∩ E j))] at hBudget
  linarith only [h, H, hBudget]

end CenteredCube.RudinDensity

#print axioms CenteredCube.RudinDensity.half_marginal_halo_mass
