import BrownianExpectation
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
namespace CubeBrownian

theorem gaussianPDFReal_eq_standardized (m x : ℝ) {v : ℝ≥0} (hv : 0 < v) :
    gaussianPDFReal m v x = φ ((x-m)/Real.sqrt (v:ℝ))/Real.sqrt (v:ℝ) := by
  have hvR : 0 < (v:ℝ) := by exact_mod_cast hv
  have hs : 0 < Real.sqrt (v:ℝ) := Real.sqrt_pos.2 hvR
  unfold φ
  simp only [gaussianPDFReal_def,NNReal.coe_one,mul_one,sub_zero]
  rw [Real.sqrt_mul (by positivity : 0 ≤ 2*Real.pi)]
  have hExp : -(x-m)^2/(2*(v:ℝ)) = -((x-m)/Real.sqrt (v:ℝ))^2/2 := by
    rw [div_pow,Real.sq_sqrt hvR.le]
    field_simp [hvR.ne'] <;> ring
  rw [hExp]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem thinLayer_weighted_standardized_limit
    (u s h m : ℕ → ℝ) (π : ℕ → ℝ → ℝ) (q : ℝ)
    (hu : ∀ n, 0 ≤ u n) (hs : ∀ n, 0 < s n)
    (hmπ : ∀ n, Measurable (π n)) (hπ : ∀ n x, x ∈ Ioi (0:ℝ) → 0 ≤ π n x ∧ π n x ≤ 1)
    (hScale : Tendsto (fun n ↦ u n / s n) atTop (𝓝 1))
    (hOffset : ∀ x ∈ Ioi (0:ℝ), Tendsto (fun n ↦ (h n+x-m n)/s n) atTop (𝓝 0))
    (hFace : ∀ x ∈ Ioi (0:ℝ), Tendsto (fun n ↦ π n x) atTop (𝓝 q)) :
    Tendsto (fun n ↦ ∫ x in Ioi (0:ℝ), Real.exp (-x)*(u n / s n)*φ ((h n+x-m n)/s n)*π n x)
      atTop (𝓝 (φ 0*q)) := by
  let C := (Real.sqrt (2*Real.pi))⁻¹
  let F (n : ℕ) (x : ℝ) := Real.exp (-x)*(u n/s n)*φ ((h n+x-m n)/s n)*π n x
  let B (x : ℝ) := (2*C)*Real.exp (-x)
  let ν := (volume : Measure ℝ).restrict (Ioi 0)
  have hφm : Measurable φ := measurable_gaussianPDFReal _ _
  have hφc : Continuous φ := by unfold φ gaussianPDFReal; fun_prop
  have hMeas (n : ℕ) : Measurable (F n) := by
    dsimp [F]
    have hInner : Measurable (fun x ↦ (h n+x-m n)/s n) := by fun_prop
    exact (((Real.measurable_exp.comp measurable_neg).mul measurable_const).mul
      (hφm.comp hInner)).mul (hmπ n)
  have hBound : ∀ᶠ n in atTop, ∀ᵐ x ∂ν, ‖F n x‖ ≤ B x := by
    filter_upwards [hScale.eventually_lt_const (by norm_num : (1:ℝ)<2)] with n hn
    filter_upwards [ae_restrict_mem measurableSet_Ioi (μ:=volume)] with x hx
    have hf := hπ n x hx
    have hD : 0 ≤ u n/s n := div_nonneg (hu n) (hs n).le
    have hDensity := phi_bounded ((h n+x-m n)/s n)
    have hFc : 0 ≤ F n x := mul_nonneg
      (mul_nonneg (mul_nonneg (Real.exp_pos _).le hD) hDensity.1) hf.1
    rw [Real.norm_eq_abs,abs_of_nonneg hFc]
    calc
      F n x ≤ ((Real.exp (-x)*2)*C)*1 :=
        mul_le_mul
          (mul_le_mul (mul_le_mul_of_nonneg_left hn.le (Real.exp_pos _).le)
            hDensity.2 hDensity.1 (by positivity)) hf.2 hf.1 (by dsimp [C]; positivity)
      _ = B x := by unfold B; ring
  have hInt : Integrable B ν := (integrableOn_exp_neg_Ioi 0).const_mul _
  have hlim : ∀ᵐ x ∂ν, Tendsto (fun n ↦ F n x) atTop (𝓝 (Real.exp (-x)*(φ 0*q))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi (μ:=volume)] with x hx
    have h0 : Tendsto (fun n ↦ φ ((h n+x-m n)/s n)) atTop (𝓝 (φ 0)) :=
      (hφc.continuousAt.tendsto.comp (hOffset x hx))
    have hT := ((hScale.const_mul (Real.exp (-x))).mul h0).mul (hFace x hx)
    simpa only [F,mul_one,mul_assoc] using hT
  have H := tendsto_integral_filter_of_dominated_convergence B
    (Eventually.of_forall fun n ↦ (hMeas n).aestronglyMeasurable) hBound hInt hlim
  change Tendsto (fun n ↦ ∫ x, F n x ∂ν) atTop (𝓝 (φ 0*q))
  have he : (∫ x, Real.exp (-x)*(φ 0*q) ∂ν) = φ 0*q := by
    rw [integral_mul_const]
    change (∫ x in Ioi (0:ℝ), Real.exp (-x))*(φ 0*q) = _
    rw [integral_exp_neg_Ioi_zero,one_mul]
  rwa [he] at H

theorem thinLayer_weighted_gaussian_limit
    (u h m : ℕ → ℝ) (v : ℕ → ℝ≥0) (π : ℕ → ℝ → ℝ) (q : ℝ)
    (hu : ∀ n, 0 ≤ u n) (hv : ∀ n, 0 < v n)
    (hmπ : ∀ n, Measurable (π n)) (hπ : ∀ n x, x ∈ Ioi (0:ℝ) → 0 ≤ π n x ∧ π n x ≤ 1)
    (hScale : Tendsto (fun n ↦ u n / Real.sqrt (v n:ℝ)) atTop (𝓝 1))
    (hOffset : ∀ x ∈ Ioi (0:ℝ),
      Tendsto (fun n ↦ (h n+x-m n)/Real.sqrt (v n:ℝ)) atTop (𝓝 0))
    (hFace : ∀ x ∈ Ioi (0:ℝ), Tendsto (fun n ↦ π n x) atTop (𝓝 q)) :
    Tendsto (fun n ↦ u n * ∫ x in Ioi (0:ℝ), Real.exp (-x)*
      gaussianPDFReal (m n) (v n) (h n+x)*π n x)
      atTop (𝓝 (φ 0*q)) := by
  have H := thinLayer_weighted_standardized_limit u (fun n ↦ Real.sqrt (v n:ℝ)) h m π q hu
    (fun n ↦ Real.sqrt_pos.2 (by exact_mod_cast hv n)) hmπ hπ hScale hOffset hFace
  apply H.congr
  intro n
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall fun x ↦ by
    dsimp only
    rw [gaussianPDFReal_eq_standardized _ _ (hv n)]
    ring
end CubeBrownian
#print axioms CubeBrownian.thinLayer_weighted_gaussian_limit
