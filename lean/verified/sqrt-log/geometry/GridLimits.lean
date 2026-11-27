import RoundedHeight

open Filter
open scoped Topology

namespace CenteredCube.RudinDensity

theorem eventually_rounded_height : ∀ᶠ n in atTop, |paperU n ^ 2 - Real.log (n:ℝ)| ≤ 1 :=
  (rounded_height_error_zero.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))).mono
    (fun _ h => h.le)

theorem eventually_paperK_pos : ∀ᶠ n in atTop, 0 < paperK n := by
  filter_upwards [paperK_tends_top_real.eventually_ge_atTop (1:ℝ)] with n h
  have hn : (0:ℝ)<(paperK n:ℝ) := zero_lt_one.trans_le h
  exact_mod_cast hn

theorem paperU_pos {n : ℕ} (hn : 0 < n) (hK : 0 < paperK n) : 0 < paperU n := by
  have hn' : (0:ℝ)<(n:ℝ) := by exact_mod_cast hn
  have hk' : (0:ℝ)<(paperK n:ℝ) := by exact_mod_cast hK
  unfold paperU
  exact div_pos (Real.sqrt_pos.2 hn') (by positivity)

theorem paperU_tends_top : Tendsto paperU atTop atTop := by
  apply tendsto_atTop.2
  intro C
  filter_upwards [eventually_rounded_height, eventually_paperK_pos, eventually_ge_atTop (2:ℕ),
    log_nat_tends_top.eventually_ge_atTop ((max C 0)^2+1)] with n he hk hn hL
  have hu := paperU_pos (by omega) hk
  have hd := (abs_le.mp he).1
  have hsq : (max C 0)^2 ≤ paperU n^2 := by linarith only [hL,hd]
  have hpos : 0 ≤ max C 0 := le_max_right _ _
  have hle : max C 0 ≤ paperU n := (sq_le_sq₀ hpos hu.le).1 hsq
  exact (le_max_left C 0).trans hle

theorem paperU_sq_over_K_zero :
    Tendsto (fun n => paperU n^2/(paperK n:ℝ)) atTop (𝓝 0) := by
  have H : Tendsto (fun n : ℕ => 4*(Real.log (n:ℝ)/paperA n)) atTop (𝓝 0) := by
    simpa only [mul_zero] using log_div_paperA_zero.const_mul 4
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds H ?_ ?_
  · exact Eventually.of_forall fun _ => by positivity
  · filter_upwards [eventually_ge_atTop (2:ℕ), eventually_rounded_height,
      paperA_tends_top.eventually_ge_atTop 4, log_nat_tends_top.eventually_ge_atTop 1]
      with n hn he ha hL
    have hp := paperA_positive n hn
    have hd := (abs_le.mp (roundedFour_error hp.le)).1
    change -(2:ℝ) ≤ (paperK n:ℝ) - paperA n at hd
    have hk : paperA n/2 ≤ (paperK n:ℝ) := by linarith only [ha,hd]
    have hu : paperU n^2 ≤ 2*Real.log (n:ℝ) := by
      linarith only [(abs_le.mp he).2,hL]
    calc
      _ ≤ (2*Real.log (n:ℝ))/(paperK n:ℝ) :=
        div_le_div_of_nonneg_right hu (by positivity)
      _ ≤ (2*Real.log (n:ℝ))/(paperA n/2) :=
        div_le_div_of_nonneg_left (by positivity) (half_pos hp) hk
      _ = _ := by ring

end CenteredCube.RudinDensity

#print axioms CenteredCube.RudinDensity.paperU_tends_top
#print axioms CenteredCube.RudinDensity.paperU_sq_over_K_zero
