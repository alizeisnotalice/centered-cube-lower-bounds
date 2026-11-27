import FarKernel
import ContinuousGap
import Mathlib.Analysis.Real.Pi.Bounds

namespace CenteredCube.RudinDensity

noncomputable def globalNu : ℝ := 1 - 3 / Real.pi
noncomputable def globalMu : ℝ := 1 - Real.sin (Real.pi/8) / (Real.pi/8)

theorem globalNu_pos : 0 < globalNu := by
  unfold globalNu
  exact sub_pos.mpr ((div_lt_one Real.pi_pos).2 Real.pi_gt_three)

theorem globalMu_pos : 0 < globalMu := by
  unfold globalMu
  have hp : 0 < Real.pi / 8 := by positivity
  exact sub_pos.mpr ((div_lt_one hp).2 (Real.sin_lt hp))

private theorem globalNu_le_one : globalNu ≤ 1 := by
  unfold globalNu
  exact sub_le_self _ (by positivity)

private theorem globalMu_le_one : globalMu ≤ 1 := by
  unfold globalMu
  have h0 : 0 ≤ Real.pi / 8 := by positivity
  have h1 : Real.pi / 8 ≤ Real.pi := by linarith [Real.pi_pos]
  exact sub_le_self _ (div_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi h0 h1) h0)

theorem window_abs_lag_le {K : ℕ} {u t s : ℝ} (hu : 4/25 ≤ u)
    (ht : |t - (K:ℝ)/4| ≤ (K:ℝ)/(100*u))
    (hs : |s - (K:ℝ)/4| ≤ (K:ℝ)/(100*u)) :
    |t-s| ≤ (K:ℝ)/8 := by
  have hu' : 0 < u := by linarith
  have ht' : 0 < 100*u := by positivity
  have ha := abs_sub_le t ((K:ℝ)/4) s
  rw [abs_sub_comm ((K:ℝ)/4) s] at ha
  have hh : |t-s| ≤ 2 * ((K:ℝ)/(100*u)) := by linarith
  apply hh.trans
  rw [← mul_div_assoc]
  apply (div_le_iff₀ ht').2
  have hr : 2 ≤ 100*u/8 := by linarith
  have hh' := mul_le_mul_of_nonneg_left hr (show 0 ≤ (K:ℝ) by positivity)
  nlinarith only [hh']

/-- Manuscript global covariance gaps, with a quantitative large-lag bound. -/
theorem covariance_global {K : ℕ} (hK : 64 ≤ K) {u t s : ℝ} (hu : 4/25 ≤ u)
    (ht : |t - (K:ℝ)/4| ≤ (K:ℝ)/(100*u))
    (hs : |s - (K:ℝ)/4| ≤ (K:ℝ)/(100*u))
    (herr : (2 * Real.pi * 64 + 8) / (K:ℝ) ≤ min globalMu globalNu / 2) :
    globalNu/2 ≤ 1 + kappa K t s ∧
    ((1:ℝ)/8 ≤ |t-s| → kappa K t s ≤ 1 - globalMu/2) ∧
    (1 ≤ |t-s| → |kappa K t s| ≤ 1/(2*|t-s|) + 8/(K:ℝ)) := by
  have hK' : 4 ≤ K := by omega
  have hu' : 3/50 ≤ u := by linarith
  have hlag := window_abs_lag_le hu ht hs
  have hfar : ∀ _h : (1:ℝ) ≤ |t-s|,
      |kappa K t s| ≤ 1/(2*|t-s|) + 8/(K:ℝ) := by
    intro h
    exact covariance_far hK' hu' ht hs (by linarith) hlag
  refine ⟨?_, ?_, hfar⟩
  · rcases le_or_gt |t-s| 64 with h | h
    · have he := (abs_le.mp (continuous_kernel hK' hu' ht hs h)).1
      have hR := Rfun_uniform_lower (t-s)
      have hn := div_le_div_of_nonneg_right (min_le_right globalMu globalNu) (by norm_num : (0:ℝ) ≤ 2)
      have hEn := herr.trans hn
      dsimp only [globalNu] at hEn ⊢
      linarith only [he, hR, hEn]
    · have hkR : (64:ℝ) ≤ (K:ℝ) := by exact_mod_cast hK
      have hA : 1 / (2*|t-s|) ≤ 1/128 :=
        one_div_le_one_div_of_le (by norm_num) (by linarith)
      have hB : 8 / (K:ℝ) ≤ 8/64 :=
        div_le_div_of_nonneg_left (by norm_num) (by norm_num) hkR
      have hL := (abs_le.mp ((hfar (by linarith)).trans
        (show 1/(2*|t-s|)+8/(K:ℝ) ≤ 1/4 by linarith [hA,hB]))).1
      linarith [globalNu_le_one]
  · intro hsmall
    rcases le_or_gt |t-s| 64 with h | h
    · have he := (abs_le.mp (continuous_kernel hK' hu' ht hs h)).2
      have hR := Rfun_uniform_upper hsmall
      have hm := div_le_div_of_nonneg_right (min_le_left globalMu globalNu) (by norm_num : (0:ℝ) ≤ 2)
      have hEm := herr.trans hm
      dsimp only [globalMu] at hEm ⊢
      linarith only [he, hR, hEm]
    · have hkR : (64:ℝ) ≤ (K:ℝ) := by exact_mod_cast hK
      have hA : 1 / (2*|t-s|) ≤ 1/128 :=
        one_div_le_one_div_of_le (by norm_num) (by linarith)
      have hB : 8 / (K:ℝ) ≤ 8/64 :=
        div_le_div_of_nonneg_left (by norm_num) (by norm_num) hkR
      have hU := (abs_le.mp ((hfar (by linarith)).trans
        (show 1/(2*|t-s|)+8/(K:ℝ) ≤ 1/4 by linarith [hA,hB]))).2
      linarith [globalMu_le_one]

theorem exists_global_cutoff :
    ∃ Kglob : ℕ, 64 ≤ Kglob ∧ ∀ K : ℕ, Kglob ≤ K →
      (2 * Real.pi * 64 + 8) / (K:ℝ) ≤ min globalMu globalNu / 2 := by
  have hpos : 0 < min globalMu globalNu / 2 :=
    div_pos (lt_min globalMu_pos globalNu_pos) (by norm_num)
  obtain ⟨j, hj⟩ := exists_nat_ge ((2 * Real.pi * 64 + 8) / (min globalMu globalNu / 2))
  refine ⟨max 64 j, le_max_left _ _, ?_⟩
  intro K hK
  have h64 : 64 ≤ K := (le_max_left 64 j).trans hK
  have hK0 : (0:ℝ) < (K:ℝ) := by exact_mod_cast (show 0 < K by omega)
  have hle : (j:ℝ) ≤ (K:ℝ) := by exact_mod_cast (le_max_right 64 j).trans hK
  apply (div_le_iff₀ hK0).2
  have H := (div_le_iff₀ hpos).1 (hj.trans hle)
  simpa [mul_comm] using H

end CenteredCube.RudinDensity

#print axioms CenteredCube.RudinDensity.covariance_global
#print axioms CenteredCube.RudinDensity.globalMu_pos
#print axioms CenteredCube.RudinDensity.globalNu_pos

#print axioms CenteredCube.RudinDensity.exists_global_cutoff
