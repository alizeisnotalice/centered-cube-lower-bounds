import BudgetLimits

open Filter
open scoped Topology

namespace CenteredCube.RudinDensity

noncomputable def marginalC : ℝ := singleLower / 2

theorem marginalC_pos : 0 < marginalC := by
  unfold marginalC singleLower
  exact div_pos (div_pos mdLower_pos (by positivity)) (by norm_num)

theorem singleUpper_nonneg : 0 ≤ singleUpper := by
  unfold singleUpper
  exact mul_nonneg (Real.exp_pos _).le mdUpper_nonneg

theorem exists_fixed_spacing :
    ∃ a : ℝ, 0 < a ∧ singleUpper/(Real.exp (a^2)-1) ≤ marginalC/4 := by
  let c := 1 + 4*singleUpper/marginalC
  have hc : 0 < c := by dsimp [c]; positivity [marginalC_pos, singleUpper_nonneg]
  refine ⟨Real.sqrt c,Real.sqrt_pos.mpr hc,?_⟩
  rw [Real.sq_sqrt hc.le]
  have h₀ : c ≤ Real.exp c-1 := by linarith [Real.add_one_le_exp c]
  have h₁ : 4*singleUpper/marginalC ≤ c := le_add_of_nonneg_left (by norm_num)
  apply (div_le_iff₀ (hc.trans_le h₀)).2
  have H := (div_le_iff₀ marginalC_pos).1 (h₁.trans h₀)
  linarith only [H]

theorem far_ratio_identity {u θ : ℝ} (hθ : 0 ≤ θ) :
    Real.exp (-(u^2)/(1+θ)) =
      (Real.exp (-(u^2/2)))^2 * Real.exp (θ*u^2/(1+θ)) := by
  rw [pow_two (Real.exp (-(u^2/2))), ← Real.exp_add, ← Real.exp_add]
  congr 1
  have hh : 1 + θ ≠ 0 := by linarith
  field_simp
  <;> ring

theorem far_normalized_zero {a : ℝ} (ha : 0 < a) :
    Tendsto (fun n => (paperGridM (paperK n) a:ℝ)*Real.exp (-(paperU n^2/2)) *
      Real.exp (lagTheta (paperK n) (paperU n)*paperU n^2/
        (1+lagTheta (paperK n) (paperU n)))) atTop (𝓝 0) := by
  have H : Tendsto (fun n => lagTheta (paperK n) (paperU n)*paperU n^2/
      (1+lagTheta (paperK n) (paperU n))) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds theta_u_sq_zero ?_ ?_
    · filter_upwards [paperU_tends_top.eventually_ge_atTop 1] with n hu
      unfold lagTheta
      positivity
    · filter_upwards [paperU_tends_top.eventually_ge_atTop 1] with n hu
      have h0 : 0 ≤ lagTheta (paperK n) (paperU n) := by unfold lagTheta; positivity
      exact div_le_self (by positivity) (by linarith)
  have E := Real.continuous_exp.continuousAt.tendsto.comp H
  simpa only [Function.comp_apply,Real.exp_zero,zero_mul] using (grid_exp_mass_zero ha).mul E

theorem eventually_overlap_ratios {a : ℝ} (ha : 0 < a) :
    ∀ᶠ n in atTop,
      singleUpper*((32*paperU n/a+1)*Real.exp (-lagDelta*paperU n^2)) ≤ marginalC/12 ∧
      singleUpper*((paperU n^3*paperU n/a+1)*Real.exp (-(1/6)*paperU n^2)) ≤ marginalC/12 ∧
      singleUpper*((paperGridM (paperK n) a:ℝ)*Real.exp (-(paperU n^2/2)) *
        Real.exp (lagTheta (paperK n) (paperU n)*paperU n^2/
          (1+lagTheta (paperK n) (paperU n)))) ≤ marginalC/6 := by
  have A : (0:ℝ) < marginalC/12 := by positivity [marginalC_pos]
  have B : (0:ℝ) < marginalC/6 := by positivity [marginalC_pos]
  have H₁ := ((mid_ratio_zero ha).const_mul singleUpper).eventually (gt_mem_nhds
    (show singleUpper*0 < marginalC/12 by simpa using A))
  have H₂ := ((outer_ratio_zero ha).const_mul singleUpper).eventually (gt_mem_nhds
    (show singleUpper*0 < marginalC/12 by simpa using A))
  have H₃ := ((far_normalized_zero ha).const_mul singleUpper).eventually (gt_mem_nhds
    (show singleUpper*0 < marginalC/6 by simpa using B))
  filter_upwards [H₁,H₂,H₃] with n hn₁ hn₂ hn₃
  exact ⟨hn₁.le,hn₂.le,hn₃.le⟩

end CenteredCube.RudinDensity

#print axioms CenteredCube.RudinDensity.exists_fixed_spacing
#print axioms CenteredCube.RudinDensity.eventually_overlap_ratios
