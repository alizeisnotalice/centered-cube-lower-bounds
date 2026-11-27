import CGFTaylor
import RateError

open MeasureTheory ProbabilityTheory Set
namespace CubeMD

private theorem exists_saddle (g : ℝ → ℝ) (y : ℝ)
    (hy : 0 < y) (hg : Differentiable ℝ g) (h0 : g 0 = 0)
    (hCurv : ∀ t ∈ Ioo 0 (2*y), deriv g t ∈ Icc (1/2 : ℝ) (3/2)) :
    ∃ q, 2*y/3 ≤ q ∧ q ≤ 2*y ∧ g q = y := by
  have h₂ : 0 < 2*y := by positivity
  obtain ⟨s,hs,he⟩ := exists_deriv_eq_slope g h₂ hg.continuous.continuousOn hg.differentiableOn
  have hEnd' : (1/2 : ℝ) ≤ (g (2*y) - g 0)/(2*y-0) := by
    rw [← he]
    exact (hCurv s hs).1
  rw [h0, sub_zero, sub_zero, le_div_iff₀ h₂] at hEnd'
  have hEnd : y ≤ g (2*y) := by linarith
  obtain ⟨q, hq, hqid⟩ := intermediate_value_Icc h₂.le hg.continuous.continuousOn
    (show y ∈ Icc (g 0) (g (2*y)) from ⟨by rw [h0]; exact hy.le, hEnd⟩)
  have hq' : 0 < q := by
    rcases hq.1.eq_or_lt with h | h
    · rw [← h,h0] at hqid
      linarith
    · exact h
  obtain ⟨u, hu, hf⟩ := exists_deriv_eq_slope g hq' hg.continuous.continuousOn hg.differentiableOn
  have hc : deriv g u ≤ 3/2 := (hCurv u ⟨hu.1,hu.2.trans_le hq.2⟩).2
  rw [hf,hqid,h0,sub_zero,sub_zero,div_le_iff₀ hq'] at hc
  exact ⟨q,by linarith only [hc],hq.2,hqid⟩

private theorem saddle_rate (C y q val : ℝ) (hC : 0 ≤ C) (hy : 0 ≤ y)
    (hq1 : 2*y/3 ≤ q) (hq2 : q ≤ 2*y)
    (hA : |y-q| ≤ C*q^2/2) (hB : |val-q^2/2| ≤ C*q^3/6) :
    |q*y-val-y^2/2| ≤ 9*C*y^3 := by
  have hq0 : 0 ≤ q := (by positivity : 0 ≤ 2*y/3).trans hq1
  have hd : |y-q| ≤ y := abs_le.mpr ⟨by linarith,by linarith⟩
  have hp2 : q^2 ≤ (2*y)^2 := pow_le_pow_left₀ hq0 hq2 _
  have hp3 : q^3 ≤ (2*y)^3 := pow_le_pow_left₀ hq0 hq2 _
  have hΔ2 : |y-q|^2 ≤ y * (C * q^2 / 2) := by
    simpa only [pow_two] using
      mul_le_mul hd hA (abs_nonneg (y-q)) hy
  have hΔ2' : |y-q|^2 ≤ 2*C*y^3 := by
    have h := mul_le_mul_of_nonneg_left hp2 (show 0 ≤ y*C/2 by positivity)
    linarith only [hΔ2, show y*(C*q^2/2) ≤ 2*C*y^3 by nlinarith only [h]]
  have hR : C*q^3/6 ≤ (4/3)*C*y^3 := by
    have h := mul_le_mul_of_nonneg_left hp3 hC
    nlinarith only [h]
  have he : q*y-val-y^2/2 = -(y-q)^2/2 -(val-q^2/2) := by ring
  have htri (x z : ℝ) : |x-z| ≤ |x|+|z| := by
    apply abs_le.mpr
    constructor <;> linarith only [le_abs_self x, neg_abs_le x, le_abs_self z, neg_abs_le z]
  rw [he]
  calc
    _ ≤ |-(y-q)^2/2| + |val-q^2/2| := htri _ _
    _ = |y-q|^2/2 + |val-q^2/2| := by norm_num [abs_div, abs_pow]
    _ ≤ _ := by linarith [hB.trans hR, show 0 ≤ C*y^3 by positivity]

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {X : Ω → ℝ}

theorem normalized_saddle_with_rate [IsProbabilityMeasure μ] (b y : ℝ) (hbn : 0 ≤ b)
    (hy : 0 < y) (hsmall : 8 * b ^ 3 * (2 * y) ≤ 1 / 2)
    (hX : AEMeasurable X μ) (hb : ∀ᵐ x ∂μ, |X x| ≤ b)
    (hmean : (∫ x, X x ∂μ) = 0) (hvar : (∫ x, X x ^ 2 ∂μ) = 1) :
    ∃ q : ℝ, 2 * y / 3 ≤ q ∧ q ≤ 2 * y ∧
      deriv (cgf X μ) q = y ∧ iteratedDeriv 2 (cgf X μ) q ∈ Icc (1/2 : ℝ) (3/2) ∧
      |q * y - cgf X μ q - y ^ 2 / 2| ≤ 72 * b ^ 3 * y ^ 3 := by
  have hIn (t : ℝ) : t ∈ interior (integrableExpSet X μ) := by
    rw [all_real_tilts hX hb]
    exact Set.mem_univ _
  have hdiff : Differentiable ℝ (deriv (cgf X μ)) :=
    fun t ↦ (analyticAt_cgf (hIn t)).deriv.differentiableAt
  have h0 : deriv (cgf X μ) 0 = 0 := by rw [deriv_cgf_zero (hIn 0), hmean, zero_div]
  have hD2 : iteratedDeriv 2 (cgf X μ) = deriv (deriv (cgf X μ)) := by
    rw [show (2 : ℕ) = 1 + 1 by rfl, iteratedDeriv_succ, iteratedDeriv_one]
  have hC : 0 ≤ 8 * b ^ 3 := by positivity
  have hCurv (t : ℝ) (ht : t ∈ Icc 0 (2 * y)) :
      iteratedDeriv 2 (cgf X μ) t ∈ Icc (1/2 : ℝ) (3/2) := by
    have e := (cgf_taylor_bounds b t hbn hX hb hmean hvar ht.1).1
    have l := (mul_le_mul_of_nonneg_left ht.2 hC).trans hsmall
    obtain ⟨e₁,e₂⟩ := abs_le.mp (e.trans l)
    exact ⟨by linarith, by linarith⟩
  have hCurv' (t : ℝ) (ht : t ∈ Ioo 0 (2 * y)) :
      deriv (deriv (cgf X μ)) t ∈ Icc (1/2 : ℝ) (3/2) := by
    rw [← hD2]
    exact hCurv t ⟨ht.1.le, ht.2.le⟩
  obtain ⟨q, hql, hqu, hqeq⟩ := exists_saddle _ y hy hdiff h0 hCurv'
  have hq0 : 0 ≤ q := (by positivity : 0 ≤ 2*y/3).trans hql
  refine ⟨q,hql,hqu,hqeq,hCurv q ⟨hq0,hqu⟩,?_⟩
  have hT := (cgf_taylor_bounds b q hbn hX hb hmean hvar hq0).2
  rw [hqeq] at hT
  calc
    _ ≤ 9 * (8 * b ^ 3) * y ^ 3 :=
      saddle_rate _ _ _ _ hC hy.le hql hqu hT.1 hT.2
    _ = _ := by ring

end CubeMD
#print axioms CubeMD.normalized_saddle_with_rate
