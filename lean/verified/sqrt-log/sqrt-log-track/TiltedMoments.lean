import Mathlib

open MeasureTheory ProbabilityTheory Set
namespace CubeMD

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {X : Ω → ℝ} {b : ℝ}

theorem all_real_tilts [IsProbabilityMeasure μ]
    (hX : AEMeasurable X μ) (hb : ∀ᵐ x ∂μ, |X x| ≤ b) :
    interior (integrableExpSet X μ) = univ := by
  suffices h : integrableExpSet X μ = univ by rw [h, interior_univ]
  apply Set.eq_univ_of_forall
  intro t
  change Integrable (fun x ↦ Real.exp (t * X x)) μ
  apply (integrable_const (Real.exp (|t| * b))).mono' (Real.continuous_exp.measurable.comp_aemeasurable (aemeasurable_const.mul hX)).aestronglyMeasurable
  filter_upwards [hb] with x hx
  change ‖Real.exp (t * X x)‖ ≤ Real.exp (|t| * b)
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
  apply Real.exp_le_exp.mpr
  exact (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left hx (abs_nonneg _))

theorem tilted_third_abs_moment [IsProbabilityMeasure μ]
    (hX : AEMeasurable X μ) (hb0 : 0 ≤ b)
    (hb : ∀ᵐ x ∂μ, |X x| ≤ b) (t : ℝ) :
    (∫ x, |X x - deriv (cgf X μ) t| ^ 3 ∂(μ.tilted (t * X ·))) ≤ 8 * b ^ 3 := by
  have ht : t ∈ interior (integrableExpSet X μ) := by
    rw [all_real_tilts hX hb]
    exact Set.mem_univ _
  let ν := μ.tilted (t * X ·)
  haveI : IsProbabilityMeasure ν :=
    isProbabilityMeasure_tilted (integrable_of_mem_integrableExpSet (interior_subset ht))
  have hbounded : ∀ᵐ x ∂ν, |X x| ≤ b :=
    (tilted_absolutelyContinuous μ (t * X ·)).ae_le hb
  have hm : |deriv (cgf X μ) t| ≤ b := by
    rw [← integral_tilted_mul_self ht]
    have hm' : ∀ᵐ x ∂ν, ‖X x‖ ≤ b := by simpa only [Real.norm_eq_abs] using hbounded
    simpa [Real.norm_eq_abs] using (norm_integral_le_of_norm_le_const hm')
  have hpow : ∀ᵐ x ∂ν, |X x - deriv (cgf X μ) t| ^ 3 ≤ 8 * b ^ 3 := by
    filter_upwards [hbounded] with x hx
    have hc : |X x - deriv (cgf X μ) t| ≤ 2 * b := by
      calc
        |X x - deriv (cgf X μ) t| ≤ |X x| + |deriv (cgf X μ) t| := by
          simpa only [Real.norm_eq_abs] using norm_sub_le (X x) (deriv (cgf X μ) t)
        _ ≤ 2 * b := by linarith
    calc
      _ ≤ (2 * b) ^ 3 := pow_le_pow_left₀ (abs_nonneg _) hc _
      _ = _ := by ring
  have hmem : MemLp X (3 : ℕ) ν := by simpa using memLp_tilted_mul ht 3
  have hInt : Integrable (fun x ↦ |X x - deriv (cgf X μ) t| ^ 3) ν := by
    simpa only [Real.norm_eq_abs, Pi.sub_apply] using
      (hmem.sub (memLp_const (deriv (cgf X μ) t))).integrable_norm_pow'
  calc
    _ ≤ ∫ _x : Ω, 8 * b ^ 3 ∂ν := integral_mono_ae hInt (integrable_const _) hpow
    _ = _ := by simp

end CubeMD
#print axioms CubeMD.all_real_tilts
#print axioms CubeMD.tilted_third_abs_moment
