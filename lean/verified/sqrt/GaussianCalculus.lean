import BrownianExpectation
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace CubeBrownian

theorem Φ_le_exp_tilt (x a : ℝ) (ha : a ≤ 0) :
    Φ x ≤ Real.exp (-a*x+a^2/2) := by
  unfold Φ
  rw [cdf_eq_real]
  have h := measure_le_le_exp_mul_mgf (μ := gaussianReal 0 1) (X := fun y : ℝ ↦ y)
    x ha (integrable_exp_mul_gaussianReal a)
  simp only [mgf_fun_id_gaussianReal, zero_mul, zero_add, NNReal.coe_one, one_mul, ← Real.exp_add] at h
  exact h

theorem Φ_eq_integral (x : ℝ) : Φ x = ∫ y in Iic x, φ y := by
  unfold Φ
  rw [cdf_eq_real,Measure.real,gaussianReal_apply_eq_integral _ one_ne_zero]
  exact ENNReal.toReal_ofReal (integral_nonneg (gaussianPDFReal_nonneg _ _))

theorem hasDerivAt_Φ (x : ℝ) : HasDerivAt Φ (φ x) x := by
  have hi : Integrable φ := integrable_gaussianPDFReal 0 1
  have hc : Continuous φ := by unfold φ gaussianPDFReal; fun_prop
  have he (y : ℝ) : Φ y = Φ 0 + ∫ t in 0..y, φ t := by
    rw [Φ_eq_integral y,Φ_eq_integral 0,← intervalIntegral.integral_Iic_sub_Iic hi.integrableOn hi.integrableOn]
    ring
  have deriv := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 x)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  rw [show Φ = (fun y ↦ Φ 0 + ∫ t in 0..y, φ t) from funext he]
  exact deriv.const_add (Φ 0)

theorem hasDerivAt_φ (x : ℝ) : HasDerivAt φ (-x*φ x) x := by
  have h (y : ℝ) : φ y = (Real.sqrt (2*Real.pi))⁻¹*Real.exp (-(y^2)/2) := by
    simp [φ,gaussianPDFReal_def]
  have h0 := (hasDerivAt_pow 2 x).neg.div_const 2
  have h1 : HasDerivAt (fun y : ℝ ↦ -(y^2)/2) (-x) x := by
    convert h0 using 1 <;> norm_num <;> ring
  have hder := h1.exp.const_mul ((Real.sqrt (2*Real.pi))⁻¹)
  have he : (Real.sqrt (2*Real.pi))⁻¹*(Real.exp (-(x^2)/2)*(-x)) = -x*φ x := by rw [h]; ring
  rw [he] at hder
  rwa [← funext h] at hder

theorem Φ_neg (x : ℝ) : Φ (-x) = 1-Φ x := by
  let G := gaussianReal 0 1
  have hNo : G {x} = 0 := gaussianReal_absolutelyContinuous 0 one_ne_zero (measure_singleton x)
  have hMap : G.map (fun x : ℝ ↦ -x) = G := by simp only [G,gaussianReal_map_neg,neg_zero]
  have hPre : (fun x : ℝ ↦ -x) ⁻¹' Iic (-x) = Ici x := by
    ext y
    change -y ≤ -x ↔ x ≤ y
    exact neg_le_neg_iff
  have h1 : G (Iic (-x)) = G (Ioi x) := by
    calc
      _ = (G.map (fun x : ℝ ↦ -x)) (Iic (-x)) := by rw [hMap]
      _ = G (Ici x) := by rw [Measure.map_apply measurable_neg measurableSet_Iic,hPre]
      _ = _ := measure_congr (Ioi_ae_eq_Ici' hNo).symm
  have h2 : G (Ioi x) = 1-G (Iic x) := by
    rw [← compl_Iic,prob_compl_eq_one_sub measurableSet_Iic]
  unfold Φ
  rw [cdf_eq_real,cdf_eq_real]
  change (G (Iic (-x))).toReal = 1-(G (Iic x)).toReal
  rw [h1,h2,ENNReal.toReal_sub_of_le (prob_le_one) ENNReal.one_ne_top,ENNReal.toReal_one]
end CubeBrownian
#print axioms CubeBrownian.Φ_neg
