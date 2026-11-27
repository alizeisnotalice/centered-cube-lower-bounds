import GridArithmetic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open Filter
open scoped Topology

namespace CenteredCube.RudinDensity

theorem log_nat_tends_top :
    Tendsto (fun n : ℕ => Real.log (n:ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

theorem log_pow_ratio_zero (p : ℝ) {q : ℝ} (hq : 0 < q) :
    Tendsto (fun n : ℕ => (Real.log (n:ℝ)) ^ p / (n:ℝ)^q) atTop (𝓝 0) :=
  (isLittleO_log_rpow_rpow_atTop p hq).tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop

theorem paperA_positive (n : ℕ) (hn : 2 ≤ n) : 0 < paperA n := by
  have h : (1:ℝ) < (n:ℝ) := by exact_mod_cast (show 1 < n by omega)
  unfold paperA
  exact div_pos (Real.sqrt_pos.2 (by linarith)) (by
    have hL := Real.log_pos h
    positivity)

theorem log_div_paperA_zero :
    Tendsto (fun n : ℕ => Real.log (n:ℝ) / paperA n) atTop (𝓝 0) := by
  have h := log_pow_ratio_zero (3/2) (q := 1/2) (by norm_num)
  have hh : Tendsto (fun n : ℕ => (90*Real.pi) *
      ((Real.log (n:ℝ)) ^ (3/2:ℝ) / (n:ℝ)^(1/2:ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero] using h.const_mul (90*Real.pi)
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (2:ℕ)] with n hn
  have hcast : (1:ℝ) < (n:ℝ) := by exact_mod_cast (show 1 < n by omega)
  have hn' : 0 < (n:ℝ) := by linarith
  have hL : 0 < Real.log (n:ℝ) := Real.log_pos hcast
  have hw : (Real.log (n:ℝ)) ^ (3/2:ℝ) =
      Real.log (n:ℝ) * Real.sqrt (Real.log (n:ℝ)) := by
    rw [Real.sqrt_eq_rpow, show (3/2:ℝ) = 1+1/2 by norm_num,
      Real.rpow_add hL, Real.rpow_one]
  rw [hw, ← Real.sqrt_eq_rpow]
  unfold paperA
  have hs : Real.sqrt (n:ℝ) ≠ 0 := (Real.sqrt_pos.2 hn').ne'
  have hsL : Real.sqrt (Real.log (n:ℝ)) ≠ 0 := (Real.sqrt_pos.2 hL).ne'
  field_simp [Real.pi_pos.ne']
  <;> ring

theorem paperA_tends_top : Tendsto paperA atTop atTop := by
  apply tendsto_atTop.2
  intro C
  have hc : 0 < max C 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  filter_upwards [eventually_ge_atTop (2:ℕ), log_nat_tends_top.eventually_ge_atTop 1,
    log_div_paperA_zero.eventually (gt_mem_nhds (show 0 < 1/max C 1 by positivity))]
    with n hn hlog hquot
  have hp : 0 < paperA n := paperA_positive n hn
  have hq := (div_lt_iff₀ hp).1 hquot
  have hq' : max C 1 < paperA n := by
    have hl : 1 < (1/max C 1) * paperA n := lt_of_le_of_lt hlog hq
    have he : (1/max C 1) * paperA n = paperA n / max C 1 := by ring
    rw [he] at hl
    simpa only [one_mul] using (lt_div_iff₀ hc).1 hl
  exact (le_max_left C 1).trans hq'.le

theorem paperK_tends_top_real : Tendsto (fun n => (paperK n:ℝ)) atTop atTop := by
  apply tendsto_atTop.2
  intro C
  filter_upwards [eventually_ge_atTop (2:ℕ), paperA_tends_top.eventually_ge_atTop (C+2)]
    with n hn ha
  have E := (abs_le.mp (roundedFour_error (paperA_positive n hn).le)).1
  change -(2:ℝ) ≤ (paperK n:ℝ)-paperA n at E
  linarith

end CenteredCube.RudinDensity

#print axioms CenteredCube.RudinDensity.log_div_paperA_zero
#print axioms CenteredCube.RudinDensity.paperA_tends_top
#print axioms CenteredCube.RudinDensity.paperK_tends_top_real
