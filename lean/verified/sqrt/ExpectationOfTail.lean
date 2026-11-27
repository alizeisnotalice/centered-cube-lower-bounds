import GaussianTailIntegrals
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace CubeBrownian

def HasReflectedTail {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (M : Ω → ℝ) (T : ℝ) : Prop :=
  ∀ x ≥ 0, μ {w | x < M w} =
    ENNReal.ofReal (Φ (-(x+T)/Real.sqrt (2*T)) +
      Real.exp (-x)*Φ ((T-x)/Real.sqrt (2*T)))

theorem exp_expectation_of_reflected_tail {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (M : Ω → ℝ) (T : ℝ)
    (hT : 0 < T) (hM : AEMeasurable M μ) (h0 : 0 ≤ᵐ[μ] M)
    (hTail : HasReflectedTail μ M T) :
    (∫⁻ w, ENNReal.ofReal (Real.exp (M w)) ∂μ) = ENNReal.ofReal (maxExpFormula T) := by
  let s := Real.sqrt (2*T)
  let f₁ : ℝ → ℝ := fun t ↦ Real.exp t*Φ (-(t+T)/s)
  let f₂ : ℝ → ℝ := fun t ↦ Φ ((T-t)/s)
  have hs : 0 < s := Real.sqrt_pos.2 (by positivity)
  have hs2 : s^2=2*T := Real.sq_sqrt (by positivity)
  have hφ (x : ℝ) : 0 ≤ Φ x := cdf_nonneg _ _
  have hf₁ (x : ℝ) : 0 ≤ f₁ x := mul_nonneg (Real.exp_pos _).le (hφ _)
  have hf₂ (x : ℝ) : 0 ≤ f₂ x := hφ _
  have hf (x : ℝ) : 0 ≤ f₁ x + f₂ x := add_nonneg (hf₁ x) (hf₂ x)
  obtain ⟨hI₁,hE₁⟩ := gaussian_I1_integrable_and_integral T s hs hs2
  obtain ⟨hI₂,hE₂⟩ := gaussian_I2_integrable_and_integral T s hs
  have he : (∫⁻ t in Ioi (0:ℝ), μ {w | t < M w} * ENNReal.ofReal (Real.exp t)) =
      ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (f₁ t + f₂ t) := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [hTail t ht.le, ← ENNReal.ofReal_mul' (Real.exp_pos _).le]
    have hE : Real.exp (-t)*Real.exp t = 1 := by rw [← Real.exp_add,neg_add_cancel,Real.exp_zero]
    congr 1
    change (Φ (-(t+T)/s)+Real.exp (-t)*f₂ t)*Real.exp t = Real.exp t*Φ (-(t+T)/s)+f₂ t
    linear_combination f₂ t*hE
  have hi₁ : IntegrableOn f₁ (Ioi (0:ℝ)) := hI₁
  have hi₂ : IntegrableOn f₂ (Ioi (0:ℝ)) := hI₂
  have hJ : ENNReal.ofReal (∫ t in Ioi (0:ℝ), f₁ t+f₂ t) =
      ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (f₁ t+f₂ t) :=
    ofReal_integral_eq_lintegral_ofReal (hi₁.add hi₂) (Eventually.of_forall hf)
  have hAdd : (∫ t in Ioi (0:ℝ), f₁ t+f₂ t) =
    (∫ t in Ioi (0:ℝ),f₁ t) + (∫ t in Ioi (0:ℝ),f₂ t) := integral_add hi₁ hi₂
  rw [exp_layercake μ M hM h0,he,← hJ,hAdd]
  have hi : 0 ≤ (∫ t in Ioi (0:ℝ), f₁ t) + (∫ t in Ioi (0:ℝ), f₂ t) :=
    add_nonneg (integral_nonneg hf₁) (integral_nonneg hf₂)
  rw [← ENNReal.ofReal_one,← ENNReal.ofReal_add zero_le_one hi]
  change ENNReal.ofReal (1+((∫ t in Ioi (0:ℝ), f₁ t)+(∫ t in Ioi (0:ℝ), f₂ t))) = _
  change (∫ t in Ioi (0:ℝ), f₁ t) = _ at hE₁
  change (∫ t in Ioi (0:ℝ), f₂ t) = _ at hE₂
  rw [hE₁,hE₂,neg_div,Φ_neg]
  have hS : T/s = Real.sqrt (T/2) := by
    symm
    apply (Real.sqrt_eq_iff_mul_self_eq (by positivity : 0 ≤ T/2) (div_nonneg hT.le hs.le)).mpr
    field_simp [hs.ne']
    nlinarith only [hs2]
  rw [hS]
  unfold maxExpFormula
  congr 1
  dsimp [s]
  ring

theorem integral_exp_of_reflected_tail {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (M : Ω → ℝ) (T : ℝ)
    (hT : 0 < T) (hM : AEMeasurable M μ) (h0 : 0 ≤ᵐ[μ] M)
    (hTail : HasReflectedTail μ M T) :
    (∫ w, Real.exp (M w) ∂μ) = maxExpFormula T := by
  have hF : 0 ≤ maxExpFormula T := by
    unfold maxExpFormula
    exact add_nonneg (mul_nonneg (by linarith) (cdf_nonneg _ _))
      (mul_nonneg (Real.sqrt_nonneg _) (phi_bounded _).1)
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall (fun _ ↦ (Real.exp_pos _).le))
    (Real.continuous_exp.measurable.comp_aemeasurable hM).aestronglyMeasurable,
    exp_expectation_of_reflected_tail μ M T hT hM h0 hTail, ENNReal.toReal_ofReal hF]
end CubeBrownian
#print axioms CubeBrownian.exp_expectation_of_reflected_tail
