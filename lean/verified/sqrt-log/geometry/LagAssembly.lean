import FourRegions

namespace CenteredCube.RudinDensity

open Finset

private theorem mid_cutoff {a u : ℝ} {m : ℕ} (h : lagBand a u m = 1) :
    (m:ℝ)*a/u ≤ 32 := by
  unfold lagBand at h
  split at h
  · norm_num at h
  split at h
  · assumption
  split at h <;> norm_num at h

private theorem outer_cutoff {a u : ℝ} {m : ℕ} (h : lagBand a u m = 2) :
    (m:ℝ)*a/u ≤ u^3 := by
  unfold lagBand at h
  split at h
  · norm_num at h
  split at h
  · norm_num at h
  split at h
  · assumption
  · norm_num at h

theorem four_region_actual_mass (M : ℕ) {a u S B L₂ L₃ L₄ : ℝ}
    (ha : 0 < a) (hu : 0 < u) (hB : 0 ≤ B)
    (h₂ : 0 ≤ L₂) (h₃ : 0 ≤ L₃) (h₄ : 0 ≤ L₄)
    (F : ℕ × ℕ → ℝ)
    (hnear : ∀ m ∈ Ico 1 M, lagBand a u m = 0 → ∀ i < M-m,
      F (i,i+m) ≤ B * Real.exp (-(a^2*(m:ℝ)^2)))
    (hmid : ∀ m ∈ Ico 1 M, lagBand a u m = 1 → ∀ i < M-m,
      F (i,i+m) ≤ L₂)
    (houter : ∀ m ∈ Ico 1 M, lagBand a u m = 2 → ∀ i < M-m,
      F (i,i+m) ≤ L₃)
    (hfar : ∀ p ∈ regionPairs M a u 3, F p ≤ L₄)
    (bnear : (M:ℝ) * B / (Real.exp (a^2)-1) ≤ S/4)
    (bmid : (M:ℝ) * (32*u/a+1)*L₂ ≤ S/12)
    (bouter : (M:ℝ) * (u^3*u/a+1)*L₃ ≤ S/12)
    (bfar : ((M:ℝ)^2/2)*L₄ ≤ S/12) :
    ∑ p ∈ forwardPairs M, F p ≤ S/2 := by
  apply four_region_sum_le_half M a u S F
  · apply (region_sum_le_lags M a u 0 F _ hnear).trans
    exact (sum_near_lag_mass _ M (fun m hm =>
      (mem_Ico.mp ((mem_filter.mp hm).1)).1) ha hB).trans bnear
  · apply (region_sum_le_lags M a u 1 F _ hmid).trans
    have hc : (((Ico 1 M).filter (fun m => lagBand a u m = 1)).card : ℝ) ≤ 32*u/a+1 :=
      card_lag_subset_of_cutoff _ ha hu (by norm_num)
        (fun m hm => mid_cutoff (mem_filter.mp hm).2)
    exact (bounded_lag_mass _ M hc h₂).trans bmid
  · apply (region_sum_le_lags M a u 2 F _ houter).trans
    have hc : (((Ico 1 M).filter (fun m => lagBand a u m = 2)).card : ℝ) ≤ u^3*u/a+1 :=
      card_lag_subset_of_cutoff _ ha hu (by positivity)
        (fun m hm => outer_cutoff (mem_filter.mp hm).2)
    exact (bounded_lag_mass _ M hc h₃).trans bouter
  · exact (sum_far_pairs_le M (regionPairs M a u 3) (filter_subset _ _) F h₄ hfar).trans bfar

end CenteredCube.RudinDensity

#print axioms CenteredCube.RudinDensity.four_region_actual_mass
