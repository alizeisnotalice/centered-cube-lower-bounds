import Cubes
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open Set MeasureTheory Filter
open scoped ENNReal Topology

namespace CenteredCube

theorem truncation_retention_sharp {n : ℕ} (hn : 1 ≤ n) :
    1 - 1 / (n : ℝ) ≤ (1 - 1 / (n : ℝ)^2)^n := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : (0 : ℝ) < n := by linarith
  have hpos : (0 : ℝ) < (n : ℝ)^2 := by positivity
  have hsq : (1 : ℝ) ≤ (n : ℝ)^2 := by nlinarith
  have hsmall : (1 : ℝ) / (n : ℝ)^2 ≤ 1 := (div_le_one hpos).mpr hsq
  have he := one_add_mul_le_pow (a := -(1 / (n : ℝ)^2))
    (show (-2 : ℝ) ≤ -(1 / (n : ℝ)^2) by linarith) n
  have hc : (n : ℝ) * (1 / (n : ℝ)^2) = 1 / n := by field_simp
  simpa only [mul_neg, hc, ← sub_eq_add_neg] using he

theorem truncation_retention_tendsto :
    Tendsto (fun n : ℕ => (1 - 1 / (n : ℝ)^2)^n) atTop (𝓝 1) := by
  have hlow : Tendsto (fun n : ℕ => 1 - 1 / (n : ℝ)) atTop (𝓝 1) := by
    simpa only [sub_zero] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    exact truncation_retention_sharp hn
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hrec : (1 : ℝ) / (n : ℝ)^2 ≤ 1 :=
      (div_le_one (by positivity)).2 (by nlinarith)
    exact pow_le_one₀ (sub_nonneg.2 hrec) (sub_le_self _ (by positivity))

/-- The actual centered cubes receive the full density-one periodic mass,
with only the exact boundary retention factor, not a fixed loss. -/
theorem sharp_transfer_of_truncated_halo {n : ℕ} (hn : 1 ≤ n) {p h : ℝ}
    (g : Space n → ℝ) (E : Set (Space n))
    (hf : Integrable ((box n ((n : ℝ)^2)).indicator g) volume)
    (hmass : absMass ((box n ((n : ℝ)^2)).indicator g) =
      ENNReal.ofReal ((2 * (n : ℝ)^2)^n))
    (hvolume : ENNReal.ofReal (p * (2 * (n : ℝ)^2 - 2)^n) ≤ volume E)
    (hE : ∀ x ∈ E, x ∈ box n ((n : ℝ)^2 - 1) ∧
      ∃ r : ℝ, 0 < r ∧ r ≤ 2 ∧ ENNReal.ofReal (Real.exp h) < cubeAverage g x r) :
    ENNReal.ofReal (Real.exp h * p * (1 - 1 / (n : ℝ)^2)^n) ≤ weakConstant n := by
  let R := (n : ℝ)^2
  let f := (box n R).indicator g
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hR : 0 < R := by dsimp [R]; positivity
  have hmassPos : 0 < (2 * R)^n := pow_pos (by positivity) _
  have havg : ∀ x ∈ E, ∃ r > 0, ENNReal.ofReal (Real.exp h) < cubeAverage f x r := by
    intro x hx
    obtain ⟨hinnerBox, r, hrad, hrad2, hval⟩ := hE x hx
    exact ⟨r, hrad, (truncated_average g hinnerBox hrad2).symm ▸ hval⟩
  have hC := lower_bound_of_average_on_set hf
    (by rw [hmass]; exact ENNReal.ofReal_pos.mpr hmassPos)
    (Real.exp_pos _) havg
  rw [hmass] at hC
  have hv : ENNReal.ofReal (Real.exp h * (p * (2 * R - 2)^n) / (2 * R)^n)
      ≤ weakConstant n := by
    rw [ENNReal.ofReal_div_of_pos hmassPos, ENNReal.ofReal_mul (Real.exp_pos _).le]
    exact (show ENNReal.ofReal (Real.exp h) * ENNReal.ofReal (p * (2 * R - 2)^n) /
        ENNReal.ofReal ((2 * R)^n) ≤ _ by gcongr).trans hC
  have hdiv : (2 * R - 2) / (2 * R) = 1 - 1 / (n : ℝ)^2 := by
    dsimp [R]
    field_simp
  refine le_trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_)) hv
  rw [← hdiv, div_pow]
  ring

#print axioms truncation_retention_sharp
#print axioms truncation_retention_tendsto
#print axioms sharp_transfer_of_truncated_halo
end CenteredCube
