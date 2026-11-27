import SqrtActualSourceMoments

namespace CenteredCubeSqrt
open Set Filter MeasureTheory
open scoped Topology BigOperators
set_option maxHeartbeats 1250000

theorem actual_q_rate_transfer {l : Filter ℕ} {v q a : ℕ→ℝ}
    (hv : Tendsto v l atTop) (hA : Tendsto (fun n => a n*v n) l (𝓝 0))
    (hV : Tendsto (fun n : ℕ => (v n)^2/(n:ℝ)) l (𝓝 0))
    (C : ℝ) (hC : 0≤C) (hQ : ∀ᶠ n in l, |q n-v n|≤C) :
    Tendsto (fun n => q n/v n) l (𝓝 1) ∧
    Tendsto (fun n => a n*q n) l (𝓝 0) ∧
    Tendsto (fun n : ℕ => q n/(n:ℝ)) l (𝓝 0) ∧
    Tendsto (fun n : ℕ => (q n)^2/(n:ℝ)) l (𝓝 0) := by
  have hVpos := hv.eventually_gt_atTop (0:ℝ)
  have ratio : Tendsto (fun n => q n/v n) l (𝓝 1) := by
    apply Metric.tendsto_nhds.2
    intro e eh
    have ht := (hv.const_div_atTop C).eventually_lt_const eh
    filter_upwards [ht,hQ,hVpos] with n he hq hp
    rw [Real.dist_eq,show q n/v n-1=(q n-v n)/v n by field_simp,
      abs_div,abs_of_pos hp]
    exact lt_of_le_of_lt (div_le_div_of_nonneg_right hq hp.le) he
  have hR : Tendsto (fun n => a n*q n) l (𝓝 0) := by
    have H := hA.mul ratio
    rw [zero_mul] at H
    refine H.congr' ?_
    filter_upwards [hVpos] with n hn
    change a n*v n*(q n/v n)=a n*q n
    field_simp
  have h2 : Tendsto (fun n : ℕ => (q n)^2/(n:ℝ)) l (𝓝 0) := by
    have H := hV.mul (ratio.pow 2)
    rw [zero_mul] at H
    refine H.congr' ?_
    filter_upwards [hVpos] with n hn
    change (v n)^2/(n:ℝ)*(q n/v n)^2=(q n)^2/(n:ℝ)
    simp only [div_pow,div_eq_mul_inv]
    have E : (v n)^2*((v n)^2)⁻¹=1 := mul_inv_cancel₀ (by positivity)
    calc
      _ = ((v n)^2*((v n)^2)⁻¹)*((q n)^2*(n:ℝ)⁻¹) := by ring
      _ = _ := by rw [E,one_mul]
  have h1 : Tendsto (fun n : ℕ => q n/(n:ℝ)) l (𝓝 0) := by
    have H := (hV.mul (tendsto_inv_atTop_zero.comp hv)).mul ratio
    simp only [zero_mul] at H
    refine H.congr' ?_
    filter_upwards [hVpos] with n hn
    change (v n)^2/(n:ℝ)*(v n)⁻¹*(q n/v n)=q n/(n:ℝ)
    simp only [div_eq_mul_inv]
    have E : (v n)^2*((v n)⁻¹)^2=1 := by rw [←mul_pow,mul_inv_cancel₀ hn.ne',one_pow]
    calc
      _ = ((v n)^2*((v n)⁻¹)^2)*(q n*(n:ℝ)⁻¹) := by ring
      _ = _ := by rw [E,one_mul]
  exact ⟨ratio,hR,h1,h2⟩

#print axioms actual_q_rate_transfer
end CenteredCubeSqrt
