import PointGrowth
import ActualGood
open Filter ProbabilityTheory
namespace CenteredCube.RudinDensity

theorem eventually_readyMD (b : ℝ) : ∀ᶠ n : ℕ in atTop, readyMD n b := by
  have ht : Tendsto (fun n : ℕ ↦ (n:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [
    ht.eventually_ge_atTop ((32 * b ^ 3)^3),
    ht.eventually_ge_atTop ((4 * Real.sqrt 6 * (30 * 64 * b ^ 3) / gaussianPDFReal 0 1 3)^3),
    ht.eventually_ge_atTop ((30 * 64 * b ^ 3)^3)] with n h0 h1 h2
  exact ⟨h0,h1,h2⟩

/-- All one-point conditions eventually hold for any positive frequency
count realizing the manuscript's rounding condition. -/
theorem eventually_onepoint_conditions :
    ∀ᶠ n : ℕ in atTop, ∀ K : ℕ, 0 < K →
      |centerScale n K^2-Real.log (n:ℝ)| ≤ 1 →
      let u := centerScale n K
      0 < n ∧ 4 ≤ K ∧ 1 ≤ u ∧ 32*u ≤ (K:ℝ) ∧
      readyMD n scoreB ∧ (2*u)^6 ≤ (n:ℝ) ∧
      72*scoreB^3*(2*u)^3/Real.sqrt (n:ℝ) ≤ 1 ∧
      u^2 + Real.log (2/singleLower) ≤ (n:ℝ)/(32*(scoreB^2+1)^2*u^4) := by
  let a0 := (32*(90*Real.pi))^2
  let a1 := (64:ℝ)
  let a2 := (576*scoreB^3)^2
  let a3 := 32*(scoreB^2+1)^2*(1+|Real.log (2/singleLower)|)
  let A := max (max a0 a1) (max a2 a3)
  have hA0 : 0 < A := lt_of_lt_of_le (by norm_num : 0 < a1)
    ((le_max_right a0 a1).trans (le_max_left _ _))
  have ht : Tendsto (fun n : ℕ ↦ (n:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun n : ℕ ↦ Real.log (n:ℝ)) atTop atTop := Real.tendsto_log_atTop.comp ht
  filter_upwards [CubeMD.eventually_log_fourth_budget A hA0, hlog.eventually_ge_atTop 2,
    eventually_readyMD scoreB, eventually_gt_atTop (0:ℕ)] with n hnA hnlog hnMD hn
  intro K hK hround
  dsimp only
  let u := centerScale n K
  have hn' : 0 < (n:ℝ) := by exact_mod_cast hn
  have hK' : 0 < (K:ℝ) := by exact_mod_cast hK
  have hu0 : 0 < u := by dsimp [u,centerScale]; positivity
  have hu1 : 1 ≤ u := by
    apply le_of_sq_le_sq _ hu0.le
    nlinarith only [hnlog, (abs_le.mp hround).1]
  have hp : u^8 ≤ (Real.log (n:ℝ)+1)^4 := by
    rw [show u^8 = (u^2)^4 by ring]
    exact pow_le_pow_left₀ (sq_nonneg _) (by linarith only [(abs_le.mp hround).2]) _
  have hA : A*u^8 ≤ (n:ℝ) := (mul_le_mul_of_nonneg_left hp hA0.le).trans hnA
  have mk (a : ℝ) (hh : a ≤ A) : a*u^8 ≤ (n:ℝ) :=
    (mul_le_mul_of_nonneg_right hh (by positivity)).trans hA
  have hB : 0 ≤ scoreB := by unfold scoreB; positivity
  obtain ⟨hscale,hwin,hmd,hbad⟩ := CubeMD.onepoint_conditions_from_power n K u scoreB singleLower
    hn' hK' hu1 hB rfl
    (mk a0 ((le_max_left a0 a1).trans (le_max_left _ _)))
    (mk a1 ((le_max_right a0 a1).trans (le_max_left _ _)))
    (mk a2 ((le_max_left a2 a3).trans (le_max_right _ _)))
    (mk a3 ((le_max_right a2 a3).trans (le_max_right _ _)))
  have hK4 : 4 ≤ K := by exact_mod_cast (show (4:ℝ) ≤ (K:ℝ) by linarith only [hu1,hscale])
  exact ⟨hn,hK4,hu1,hscale,hnMD,hwin,hmd,hbad⟩
end CenteredCube.RudinDensity
#print axioms CenteredCube.RudinDensity.eventually_onepoint_conditions
