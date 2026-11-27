import LindebergReplacement
import Mathlib.MeasureTheory.Group.IntegralConvolution

open MeasureTheory
open scoped MeasureTheory

namespace CubeSqrtProbability

noncomputable def sumLaw {E : Type*} [AddMonoid E] [MeasurableSpace E]
    (μ : Measure E) : ℕ → Measure E
  | 0 => Measure.dirac 0
  | n+1 => sumLaw μ n ∗ μ

instance sumLaw_probability {E : Type*} [AddMonoid E] [MeasurableSpace E]
    [MeasurableAdd₂ E] (μ : Measure E) [IsProbabilityMeasure μ] (n : ℕ) :
    IsProbabilityMeasure (sumLaw μ n) := by
  induction n with
  | zero => unfold sumLaw; infer_instance
  | succ n ih =>
    change IsProbabilityMeasure (sumLaw μ n ∗ μ)
    letI := ih
    infer_instance

theorem integrate_shift_convolution_comparison
    {E : Type*} [AddCommMonoid E] [MeasurableSpace E] [MeasurableAdd₂ E]
    (ρ μ ν : Measure E) [IsProbabilityMeasure ρ]
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (F : E → ℝ) (hm : Measurable F) (B e : ℝ)
    (hB : ∀ x, |F x| ≤ B)
    (h : ∀ z, |(∫ x, F (z+x) ∂μ) - ∫ x, F (z+x) ∂ν| ≤ e) (z : E) :
    |(∫ x, F (z+x) ∂(ρ∗μ)) - ∫ x, F (z+x) ∂(ρ∗ν)| ≤ e := by
  have hInt (τ : Measure E) [IsProbabilityMeasure τ] : Integrable (fun x ↦ F (z+x)) τ :=
    (integrable_const B).mono' (hm.comp (measurable_const.add measurable_id)).aestronglyMeasurable
      (ae_of_all _ fun x ↦ by simpa only [Real.norm_eq_abs] using hB (z+x))
  rw [integral_conv (hInt (ρ∗μ)),integral_conv (hInt (ρ∗ν))]
  let f : E × E → ℝ := fun w ↦ F (z+(w.1+w.2))
  have hProd (τ : Measure E) [IsProbabilityMeasure τ] : Integrable f (ρ.prod τ) :=
    (integrable_const B).mono' (hm.comp (by fun_prop : Measurable (fun w : E × E ↦ z+(w.1+w.2)))).aestronglyMeasurable
      (ae_of_all _ fun w ↦ by simpa only [Real.norm_eq_abs] using hB (z+(w.1+w.2)))
  have hP := replacement_under_common_background ρ μ ν f f e (hProd μ) (hProd ν)
    (ae_of_all _ fun y ↦ by simpa only [f,add_assoc] using h (z+y))
  rwa [integral_prod f (hProd μ),integral_prod f (hProd ν)] at hP

/-- Actual convolution of iid laws magnifies a uniformly bounded single
replacement error by at most the number of summands. -/
theorem sumLaw_shift_comparison
    {E : Type*} [AddCommMonoid E] [MeasurableSpace E] [MeasurableAdd₂ E]
    (μ ν : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (F : E → ℝ) (hm : Measurable F) (B e : ℝ)
    (hB : ∀ x, |F x| ≤ B)
    (h : ∀ z, |(∫ x, F (z+x) ∂μ) - ∫ x, F (z+x) ∂ν| ≤ e)
    (n : ℕ) (z : E) :
    |(∫ x, F (z+x) ∂(sumLaw μ n)) - ∫ x, F (z+x) ∂(sumLaw ν n)| ≤ (n:ℝ)*e := by
  induction n generalizing z with
  | zero => simp [sumLaw]
  | succ n ih =>
    change |(∫ x, F (z+x) ∂(sumLaw μ n ∗ μ)) -
        (∫ x, F (z+x) ∂(sumLaw ν n ∗ ν))| ≤ _
    have hstep := integrate_shift_convolution_comparison (sumLaw μ n) μ ν F hm B e hB h z
    have hprior := integrate_shift_convolution_comparison ν (sumLaw μ n) (sumLaw ν n)
      F hm B ((n:ℝ)*e) hB ih z
    rw [Measure.conv_comm ν (sumLaw μ n), Measure.conv_comm ν (sumLaw ν n)] at hprior
    calc
      _ ≤ |(∫ x, F (z+x) ∂(sumLaw μ n ∗ μ)) - (∫ x, F (z+x) ∂(sumLaw μ n ∗ ν))| +
          |(∫ x, F (z+x) ∂(sumLaw μ n ∗ ν)) - (∫ x, F (z+x) ∂(sumLaw ν n ∗ ν))| :=
        abs_sub_le _ _ _
      _ ≤ e + (n:ℝ)*e := add_le_add hstep hprior
      _ = _ := by push_cast; ring

end CubeSqrtProbability
#print axioms CubeSqrtProbability.sumLaw_shift_comparison
