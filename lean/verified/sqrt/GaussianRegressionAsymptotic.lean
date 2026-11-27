import GaussianResidualMoments

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology ProbabilityTheory
namespace CubeBrownian

lemma tendsto_div_zero_of_bounded_num
    (s V : ℕ → ℝ) (hV : Tendsto V atTop atTop)
    (C : ℝ) (hC : ∀ᶠ n in atTop, |s n| ≤ C) :
    Tendsto (fun n ↦ s n/V n) atTop (𝓝 0) := by
  apply squeeze_zero_norm' _ (hV.const_div_atTop C)
  filter_upwards [hC,hV.eventually_gt_atTop 0] with n hn hpos
  rw [Real.norm_eq_abs,abs_div,abs_of_pos hpos]
  exact div_le_div_of_nonneg_right hn hpos.le

/-- Bounded baseline mean (after subtracting the threshold) and bounded
baseline-to-difference covariance make both regression corrections vanish
when the baseline variance diverges. -/
theorem gaussian_regression_corrections_vanish
    (a r V c : ℕ → ℝ) (x A R : ℝ)
    (hV : Tendsto V atTop atTop) (ha : ∀ᶠ n in atTop, |a n| ≤ A)
    (hr : ∀ᶠ n in atTop, |r n| ≤ R) (hc : ∀ n, r n = c n * V n) :
    Tendsto (fun n ↦ c n*(x-a n)) atTop (𝓝 0) ∧
      Tendsto (fun n ↦ (c n)^2*V n) atTop (𝓝 0) := by
  have hS : ∀ᶠ n in atTop, |r n*(x-a n)| ≤ R*(|x|+A) := by
    filter_upwards [ha,hr] with n hn hR
    rw [abs_mul]
    exact mul_le_mul hR ((abs_sub _ _).trans (add_le_add_right hn _)) (abs_nonneg _) (le_trans (abs_nonneg _) hR)
  have hQ : ∀ᶠ n in atTop, |(r n)^2| ≤ R^2 := by
    filter_upwards [hr] with n hn
    rw [abs_of_nonneg (sq_nonneg _),← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hn 2
  have H1 := tendsto_div_zero_of_bounded_num (fun n ↦ r n*(x-a n)) V hV _ hS
  have H2 := tendsto_div_zero_of_bounded_num (fun n ↦ (r n)^2) V hV _ hQ
  constructor
  · apply H1.congr'
    filter_upwards [hV.eventually_gt_atTop 0] with n hn
    rw [hc]
    field_simp
  · apply H2.congr'
    filter_upwards [hV.eventually_gt_atTop 0] with n hn
    rw [hc]
    field_simp

/-- Raw projected moment limits imply the same limits for the true scalar
Gaussian regression laws when baseline variances diverge. -/
theorem gaussian_regression_projected_moment_limits
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (μ : ℕ → Measure Ω) (Z : ℕ → Ω → ℝ) (D : ℕ → Ω → E) (c : ℕ → E)
    (hZD : ∀ n, HasGaussianLaw (fun w ↦ (Z n w,D n w)) (μ n))
    (L : StrongDual ℝ E)
    (hc : ∀ n, cov[Z n,L ∘ D n;μ n] = L (c n) * Var[Z n; μ n])
    (x A R m V : ℝ)
    (hV : Tendsto (fun n ↦ Var[Z n;μ n]) atTop atTop)
    (hA : ∀ᶠ n in atTop, |∫ w, Z n w ∂(μ n)| ≤ A)
    (hR : ∀ᶠ n in atTop, |cov[Z n,L ∘ D n;μ n]| ≤ R)
    (hm : Tendsto (fun n ↦ ∫ w, L (D n w) ∂(μ n)) atTop (𝓝 m))
    (hv : Tendsto (fun n ↦ Var[L ∘ D n;μ n]) atTop (𝓝 V)) :
    Tendsto (fun n ↦ ∫ w, L (D n w-Z n w • c n+x • c n) ∂(μ n)) atTop (𝓝 m) ∧
      Tendsto (fun n ↦ Var[fun w ↦ L (D n w-Z n w • c n+x • c n); μ n]) atTop (𝓝 V) := by
  have H := gaussian_regression_corrections_vanish (fun n ↦ ∫ w, Z n w ∂(μ n))
    (fun n ↦ cov[Z n,L ∘ D n;μ n]) (fun n ↦ Var[Z n;μ n]) (fun n ↦ L (c n)) x A R
    hV hA hR hc
  have hEq n := gaussian_regression_projected_moments (μ n) (Z n) (D n) (c n) (hZD n) L (hc n) x
  constructor
  · simp_rw [fun n ↦ (hEq n).1]
    simpa only [add_zero] using hm.add H.1
  · simp_rw [fun n ↦ (hEq n).2]
    simpa only [sub_zero] using hv.sub H.2

end CubeBrownian
#print axioms CubeBrownian.gaussian_regression_corrections_vanish
#print axioms CubeBrownian.gaussian_regression_projected_moment_limits
