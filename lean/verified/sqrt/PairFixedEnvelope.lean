import PairFixedDistance
import PairUniformPrefactor
open MeasureTheory ProbabilityTheory Filter Set CubeBrownian
open scoped NNReal ENNReal Topology ProbabilityTheory
namespace CubeSqrtPair

theorem kernel_fixed_distance_exp_upper (H θ v κ r c D : ℝ) (n : ℕ)
    (hv : 0 < v) (hθ : 0 ≤ θ)
    (hgap : c*r-D ≤ v*(1-κ))
    (hH : H^n ≤ Real.exp (-(θ*(1-κ)/4))) :
    H^n ≤ Real.exp (-((θ/v)*(c*r-D)/4)) := by
  apply hH.trans (Real.exp_le_exp.mpr _)
  have h := mul_le_mul_of_nonneg_left hgap (div_nonneg hθ hv.le)
  have he : θ/v*(v*(1-κ)) = θ*(1-κ) := by field_simp [hv.ne']
  rw [he] at h
  linarith only [h]

/-- Sharp fixed-distance envelope, expressed as an eventually arbitrary
slack bound; no growing-distance uniformity is inferred from it. -/
theorem pair_fixed_distance_limit_bound
    (X a ρ g D : ℕ → ℝ) (c r w : ℝ)
    (ha : Tendsto a atTop (𝓝 0))
    (hρ : Tendsto ρ atTop (𝓝 1))
    (hg : Tendsto g atTop (𝓝 1))
    (hD : Tendsto D atTop (𝓝 (16/(3*w))))
    (hX : ∀ᶠ n in atTop, X n ≤ (φ 0+240*a n)*ρ n *
      Real.exp (-(g n*(c*r-D n)/4)))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, X n ≤ φ 0*Real.exp (4/(3*w))*Real.exp (-c*r/4)+ε := by
  have hm := (tendsto_const_nhds (x:=φ 0)).add (ha.const_mul (240:ℝ))
  have hDiff := (tendsto_const_nhds (x:=c*r)).sub hD
  have hExp := Real.continuous_exp.continuousAt.tendsto.comp
    ((hg.mul hDiff).div_const (4:ℝ)).neg
  have hT := (hm.mul hρ).mul hExp
  have hC : -(1*(c*r-16/(3*w))/4) = 4/(3*w)+(-c*r/4) := by ring
  have H : Tendsto (fun n ↦ (φ 0+240*a n)*ρ n * Real.exp (-(g n*(c*r-D n)/4)))
      atTop (𝓝 (φ 0*Real.exp (4/(3*w))*Real.exp (-c*r/4))) := by
    simpa only [Function.comp_apply,mul_zero,add_zero,mul_one,hC,Real.exp_add,mul_assoc]
      using hT
  filter_upwards [hX,H.eventually_lt_const (lt_add_of_pos_right _ hε)] with n hn hh
  exact hn.trans hh.le

end CubeSqrtPair
#print axioms CubeSqrtPair.kernel_fixed_distance_exp_upper
#print axioms CubeSqrtPair.pair_fixed_distance_limit_bound
