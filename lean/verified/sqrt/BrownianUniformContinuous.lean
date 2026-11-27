import BrownianMaximalBound
open Filter Set MeasureTheory ProbabilityTheory
open scoped Topology NNReal
namespace CubeBrownian

theorem maxExpFormula_div_uniform {lo hi : ℝ} (hlo : 0 < lo) (hhi : 0 < hi)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ k ∈ Icc lo hi,
      |maxExpFormula (k*T) / T - k| < ε := by
  have hp : 0 < ε/hi := div_pos hε hhi
  obtain ⟨s, hs⟩ := eventually_atTop.mp
    (Metric.tendsto_nhds.mp maxExpFormula_div_tendsto_one (ε/hi) hp)
  filter_upwards [eventually_ge_atTop (max 1 (s/lo))] with T hT k hk
  have hTpos : 0 < T := zero_lt_one.trans_le ((le_max_left _ _).trans hT)
  have hkpos : 0 < k := hlo.trans_le hk.1
  have hsk : s ≤ k*T := calc
    s ≤ T*lo := (div_le_iff₀ hlo).mp ((le_max_right _ _).trans hT)
    _ ≤ T*k := mul_le_mul_of_nonneg_left hk.1 hTpos.le
    _ = k*T := mul_comm _ _
  have he := hs _ hsk
  rw [Real.dist_eq] at he
  have hcalc : maxExpFormula (k*T) / T - k =
      k*(maxExpFormula (k*T)/(k*T)-1) := by
    field_simp [hTpos.ne',hkpos.ne']
  rw [hcalc, abs_mul, abs_of_nonneg hkpos.le]
  calc
    k*|maxExpFormula (k*T)/(k*T)-1| < k*(ε/hi) :=
      mul_lt_mul_of_pos_left he hkpos
    _ ≤ hi*(ε/hi) := mul_le_mul_of_nonneg_right hk.2 hp.le
    _ = ε := by field_simp

theorem paperBrownian_scaled_expectation {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B μ)
    (k T : ℝ≥0) (hk : 0 < k) (hT : 0 < T) :
    (∫ w, Real.exp (⨆ t : Icc (0:ℝ≥0) T,
      Real.sqrt (2*(k:ℝ)) * B t w - (k:ℝ)*(t.1:ℝ)) ∂μ) =
      maxExpFormula ((k:ℝ)*(T:ℝ)) := by
  let C := fun t w ↦ (Real.sqrt ((k⁻¹:ℝ≥0):ℝ))⁻¹ * B (k⁻¹*t) w
  have hC : IsBrownianReal C μ := hB.smul (c:=k⁻¹) (by positivity)
  have H := paperBrownian_exp_expectation_complete μ hC (k*T) (mul_pos hk hT)
  push_cast at H
  rw [← H]
  apply integral_congr_ae
  filter_upwards with w
  congr 1
  rw [← sSup_range, ← sSup_range]
  congr 1
  have hOne (t : ℝ≥0) : k⁻¹*(k*t) = t := by
    rw [← mul_assoc,inv_mul_cancel₀ hk.ne',one_mul]
  have hTwo (t : ℝ≥0) : k*(k⁻¹*t) = t := by
    rw [← mul_assoc,mul_inv_cancel₀ hk.ne',one_mul]
  have hCoeff : Real.sqrt 2 * (Real.sqrt ((k⁻¹:ℝ≥0):ℝ))⁻¹ = Real.sqrt (2*(k:ℝ)) := by
    push_cast
    rw [Real.sqrt_inv,inv_inv,Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
  have hVal (t : ℝ≥0) :
      Real.sqrt 2 * C (k*t) w - ((k*t : ℝ≥0) : ℝ) =
        Real.sqrt (2*(k:ℝ)) * B t w - (k:ℝ)*(t:ℝ) := by
    dsimp only [C]
    rw [hOne, ← mul_assoc, hCoeff]
    rfl
  ext y
  constructor
  · rintro ⟨t,rfl⟩
    refine ⟨⟨k*(t:ℝ≥0),zero_le,mul_le_mul_of_nonneg_left t.2.2 (zero_le)⟩,?_⟩
    exact hVal t
  · rintro ⟨t,rfl⟩
    refine ⟨⟨k⁻¹*(t:ℝ≥0),zero_le,?_⟩,?_⟩
    · calc
        k⁻¹*(t:ℝ≥0) ≤ k⁻¹*(k*T) := mul_le_mul_of_nonneg_left t.2.2 (zero_le)
        _ = T := hOne T
    · have he := (hVal (k⁻¹*(t:ℝ≥0))).symm
      rwa [hTwo] at he
end CubeBrownian
