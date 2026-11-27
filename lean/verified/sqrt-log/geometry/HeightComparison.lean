import GridLimits

open Filter
open scoped Topology

namespace CenteredCube.RudinDensity

theorem height_comparison {n : ℕ} {u : ℝ} (hn : 0 < n)
    (h : |u^2 - Real.log (n:ℝ)| ≤ 1) :
    Real.exp (-(1/2)) ≤ Real.sqrt (n:ℝ) * Real.exp (-(u^2/2)) ∧
      Real.sqrt (n:ℝ) * Real.exp (-(u^2/2)) ≤ Real.exp (1/2) := by
  have hn' : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have he : Real.sqrt (n:ℝ) = Real.exp (Real.log (n:ℝ)/2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hn']
    congr 1
    ring
  rw [he, ← Real.exp_add]
  have hh := abs_le.mp h
  exact ⟨Real.exp_le_exp.mpr (by linarith only [hh.2]),
    Real.exp_le_exp.mpr (by linarith only [hh.1])⟩

theorem grid_exp_mass_upper {n : ℕ} {a : ℝ} (hn : 0 < n) (ha : 0 < a) (hk : 0 < paperK n)
    (hg : 2 ≤ (paperK n:ℝ)/(100*a)) (he : |paperU n^2-Real.log (n:ℝ)| ≤ 1) :
    (paperGridM (paperK n) a:ℝ)*Real.exp (-(paperU n^2/2)) ≤
      Real.exp (1/2)/(3000*Real.pi*a*paperU n) := by
  have hK := paperK_center_relation hn hk
  have hU := paperU_pos hn hk
  have hM := (paperGrid_card_bound (paperK n) ha hg).2
  have hu := (height_comparison hn he).2
  have h0 : 0 < 3000*Real.pi*a*paperU n := by positivity
  have hE : 3*((paperK n:ℝ)/(100*a))*Real.exp (-(paperU n^2/2)) =
      (Real.sqrt (n:ℝ)*Real.exp (-(paperU n^2/2)))/(3000*Real.pi*a*paperU n) := by
    nth_rw 1 [hK]
    field_simp
    <;> ring
  exact (mul_le_mul_of_nonneg_right hM (Real.exp_pos _).le).trans
    (hE.le.trans (div_le_div_of_nonneg_right hu h0.le))

theorem grid_exp_mass_lower {n : ℕ} {a : ℝ} (hn : 0 < n) (ha : 0 < a) (hk : 0 < paperK n)
    (hg : 2 ≤ (paperK n:ℝ)/(100*a)) (he : |paperU n^2-Real.log (n:ℝ)| ≤ 1) :
    Real.exp (-(1/2))/(9000*Real.pi*a*paperU n) ≤
      (paperGridM (paperK n) a:ℝ)*Real.exp (-(paperU n^2/2)) := by
  have hK := paperK_center_relation hn hk
  have hU := paperU_pos hn hk
  have hM := (paperGrid_card_bound (paperK n) ha hg).1
  have hu := (height_comparison hn he).1
  have h0 : 0 < 9000*Real.pi*a*paperU n := by positivity
  have hE : (paperK n:ℝ)/(100*a)*Real.exp (-(paperU n^2/2)) =
      (Real.sqrt (n:ℝ)*Real.exp (-(paperU n^2/2)))/(9000*Real.pi*a*paperU n) := by
    nth_rw 1 [hK]
    field_simp
    <;> ring
  exact (div_le_div_of_nonneg_right hu h0.le).trans
    (hE.ge.trans (mul_le_mul_of_nonneg_right hM (Real.exp_pos _).le))

theorem eventually_grid_large {a : ℝ} (ha : 0 < a) :
    ∀ᶠ n in atTop, 2 ≤ (paperK n:ℝ)/(100*a) := by
  filter_upwards [paperK_tends_top_real.eventually_ge_atTop (2*(100*a))] with n hn
  exact (le_div_iff₀ (by positivity)).2 hn

theorem grid_exp_mass_zero {a : ℝ} (ha : 0 < a) :
    Tendsto (fun n => (paperGridM (paperK n) a:ℝ)*Real.exp (-(paperU n^2/2))) atTop (𝓝 0) := by
  have h0 : Tendsto (fun n : ℕ => (paperU n)⁻¹) atTop (𝓝 0) :=
    paperU_tends_top.inv_tendsto_atTop
  have hU : Tendsto (fun n : ℕ => (Real.exp (1/2)/(3000*Real.pi*a))* (paperU n)⁻¹) atTop (𝓝 0) := by
    simpa only [mul_zero] using h0.const_mul (Real.exp (1/2)/(3000*Real.pi*a))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hU ?_ ?_
  · exact Eventually.of_forall (fun n => by positivity)
  · filter_upwards [eventually_ge_atTop (2:ℕ),eventually_paperK_pos,
      eventually_rounded_height,eventually_grid_large ha] with n hn hk he hg
    have H := grid_exp_mass_upper (show 0 < n by omega) ha hk hg he
    exact H.trans_eq (by rw [← div_eq_mul_inv, div_div])

end CenteredCube.RudinDensity

#print axioms CenteredCube.RudinDensity.height_comparison
#print axioms CenteredCube.RudinDensity.grid_exp_mass_lower
#print axioms CenteredCube.RudinDensity.grid_exp_mass_zero
