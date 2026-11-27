import BrownianGridCDF
open MeasureTheory Set
namespace CubeBrownian

theorem partialSum_pathDifferences {n : ℕ} (f : ℕ → ℝ) (k : ℕ) :
    partialSum (n:=n) k (fun i ↦ f ((i:ℕ)+1) - f i) =
      f (min (k+1) n) - f 0 := by
  classical
  unfold partialSum
  rw [Finset.sum_filter, Fin.sum_univ_eq_sum_range (fun i ↦ if i ≤ k then f (i+1)-f i else 0),
    ← Finset.sum_filter]
  have hs : (Finset.range n).filter (fun i ↦ i ≤ k) = Finset.range (min (k+1) n) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, lt_min_iff]
    omega
  rw [hs, Finset.sum_range_sub]

theorem total_pathDifferences {n : ℕ} (f : ℕ → ℝ) :
    (∑ (i : Fin n), (f ((i:ℕ)+1)-f i)) = f n-f 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun i ↦ f (i+1)-f i), Finset.sum_range_sub]
end CubeBrownian
