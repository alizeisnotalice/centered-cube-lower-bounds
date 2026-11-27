import BrownianExpectation
import Mathlib.MeasureTheory.Measure.Tilted
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
namespace CubeBrownian

theorem gaussian_zero_tilt_eq_shift (a : ℝ) (v : ℝ≥0) (hv : 0 < v) :
    (gaussianReal 0 v).tilted (fun x ↦ a*x) = gaussianReal (a*(v:ℝ)) v := by
  have hvr : 0 < (v:ℝ) := by exact_mod_cast hv
  have hmgf : (∫ x, Real.exp (a*x) ∂(gaussianReal 0 v)) =
      Real.exp ((v:ℝ)*a^2/2) := by
    change mgf (fun x ↦ x) (gaussianReal 0 v) a = _
    rw [mgf_fun_id_gaussianReal]
    simp
  let f : ℝ → ℝ≥0∞ := fun x ↦ ENNReal.ofReal (Real.exp (a*x)/Real.exp ((v:ℝ)*a^2/2))
  have hf : Measurable f := by dsimp only [f]; fun_prop
  have hL : (gaussianReal 0 v).tilted (fun x ↦ a*x) = ((gaussianReal 0 v).withDensity f) := by
    unfold Measure.tilted
    rw [hmgf]
  rw [hL, gaussianReal_of_var_ne_zero 0 hv.ne', gaussianReal_of_var_ne_zero _ hv.ne',
    ← withDensity_mul _ (measurable_gaussianPDF _ _) hf]
  apply withDensity_congr_ae
  filter_upwards with x
  change gaussianPDF 0 v x * f x = gaussianPDF (a*(v:ℝ)) v x
  dsimp only [f]
  rw [gaussianPDF_def, gaussianPDF_def, ← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _)]
  congr 1
  simp only [gaussianPDFReal_def, sub_zero]
  rw [← Real.exp_sub, mul_assoc, ← Real.exp_add]
  congr 2
  field_simp [hvr.ne'] <;> ring

theorem endpoint_brownian_tilt (T : ℝ≥0) (hT : 0 < T) :
    (gaussianReal 0 (2*T)).tilted (fun x ↦ -(x/2)) =
      gaussianReal (-(T:ℝ)) (2*T) := by
  have hfun : (fun x : ℝ ↦ -(x/2)) = fun x ↦ (-1/2)*x := by funext x; ring
  rw [hfun, gaussian_zero_tilt_eq_shift _ _ (by positivity)]
  congr 1
  push_cast
  ring
end CubeBrownian
#print axioms CubeBrownian.gaussian_zero_tilt_eq_shift
