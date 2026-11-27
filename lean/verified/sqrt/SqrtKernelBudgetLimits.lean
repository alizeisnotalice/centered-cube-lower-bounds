import SqrtKernelEventually

namespace CenteredCubeSqrt
open Set MeasureTheory Filter Topology
open scoped BigOperators Interval
set_option maxHeartbeats 750000

noncomputable def paperFarRawBudget (B K : ℝ) : ℝ :=
  Real.sqrt ((1/12+1/(6*B^2))*(1/48+1/(6*B^2)))+1/(12*B^2)+1/(2*K)

theorem paper_kernel_budgets_tendsto (B K M E : ℕ→ℝ)
    (hB : Tendsto (fun n => (B n)⁻¹) atTop (𝓝 0))
    (hK : Tendsto (fun n => (K n)⁻¹) atTop (𝓝 0))
    (hM : Tendsto (fun n => (M n)⁻¹) atTop (𝓝 0))
    (hE : Tendsto E atTop (𝓝 0)) :
    Tendsto (fun n => paperFarRawBudget (B n) (K n)) atTop (𝓝 (1/24)) ∧
    Tendsto (fun n => 2/(3*(B n)^2)+2/K n+E n) atTop (𝓝 0) ∧
    Tendsto (fun n => 100/261-(48/(29*(M n)^3))/3-(1/(3*(B n)^2)+2/K n+E n))
      atTop (𝓝 (100/261)) := by
  have b : Tendsto (fun n => ((B n)⁻¹)^2) atTop (𝓝 0) := by simpa using hB.pow 2
  have m : Tendsto (fun n => ((M n)⁻¹)^3) atTop (𝓝 0) := by simpa using hM.pow 3
  have e₁ (s p q : ℝ) (i : ℕ) : s/(p*q^i)=(s/p)*(q⁻¹)^i := by rw [div_eq_mul_inv, mul_inv,inv_pow]; ring
  have e₂ (s q : ℝ) : s/q=s*q⁻¹ := div_eq_mul_inv s q
  constructor
  · have r₁ : Tendsto (fun n => (1/12:ℝ)+(1/6)*((B n)⁻¹)^2) atTop (𝓝 (1/12)) := by
      simpa only [mul_zero,add_zero] using (tendsto_const_nhds (x:=(1/12:ℝ))).add (b.const_mul (1/6))
    have r₂ : Tendsto (fun n => (1/48:ℝ)+(1/6)*((B n)⁻¹)^2) atTop (𝓝 (1/48)) := by
      simpa only [mul_zero,add_zero] using (tendsto_const_nhds (x:=(1/48:ℝ))).add (b.const_mul (1/6))
    have hr : Real.sqrt ((1/12)*(1/48))=1/24 := by
      rw [show (1/12:ℝ)*(1/48)=(1/24)^2 by norm_num, Real.sqrt_sq (by norm_num)]
    have H := ((Real.continuous_sqrt.continuousAt.tendsto.comp (r₁.mul r₂)).add (b.const_mul (1/12))).add
      (hK.const_mul (1/2))
    have ea (n : ℕ) : paperFarRawBudget (B n) (K n) =
        Real.sqrt ((1/12+(1/6)*((B n)⁻¹)^2)*(1/48+(1/6)*((B n)⁻¹)^2))+
          (1/12)*((B n)⁻¹)^2+(1/2)*(K n)⁻¹ := by
      unfold paperFarRawBudget
      rw [e₁,e₁,show 1/(2*K n)=(1/2)*(K n)⁻¹ by rw [div_eq_mul_inv,mul_inv]; ring]
    simp only [ea]
    simpa only [Function.comp_def,hr,mul_zero,add_zero] using H
  constructor
  · have H := ((b.const_mul (2/3)).add (hK.const_mul 2)).add hE
    simp_rw [e₁,e₂ 2 (K _)]
    simpa using H
  · have hT := (m.const_mul (48/29:ℝ)).div_const 3
    have hA := ((b.const_mul (1/3)).add (hK.const_mul 2)).add hE
    have H := ((tendsto_const_nhds (x:=(100/261:ℝ))).sub hT).sub hA
    simp_rw [e₁,e₂ 2 (K _)]
    simpa using H

#print axioms paper_kernel_budgets_tendsto
end CenteredCubeSqrt
