import TiltedMoments
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace CubeMD

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {X : Ω → ℝ}

private noncomputable def tiltRaw (X : Ω → ℝ) (μ : Measure Ω) (k : ℕ) (t : ℝ) : ℝ :=
  (∫ x, X x ^ k * Real.exp (t * X x) ∂μ) / mgf X μ t

private theorem deriv_tiltRaw (h : ∀ t, t ∈ interior (integrableExpSet X μ)) (k : ℕ) (t : ℝ) :
    HasDerivAt (tiltRaw X μ k) (tiltRaw X μ (k+1) t - tiltRaw X μ k t * tiltRaw X μ 1 t) t := by
  have hd := hasDerivAt_integral_pow_mul_exp_real (h t) k
  have hM : 0 < mgf X μ t := mgf_pos (integrable_of_mem_integrableExpSet (interior_subset (h t)))
  have h' := hd.div (hasDerivAt_mgf (h t)) hM.ne'
  convert h' using 1
  · rfl
  · simp only [tiltRaw, pow_one]
    field_simp [hM.ne'] <;> ring

private theorem tiltRaw_eq (k : ℕ) (t : ℝ) :
    tiltRaw X μ k t = ∫ x, X x ^ k ∂(μ.tilted (t * X ·)) := by
  rw [integral_tilted_mul_eq_mgf]
  unfold tiltRaw
  rw [← integral_div]
  congr 1
  ext x
  simp only [smul_eq_mul]
  ring

theorem third_cgf_central_cube (b : ℝ)
    (hX : AEMeasurable X μ) (hb : ∀ᵐ x ∂μ, |X x| ≤ b) (t : ℝ) :
    iteratedDeriv 3 (cgf X μ) t =
      ∫ x, (X x - deriv (cgf X μ) t)^3 ∂(μ.tilted (t * X ·)) := by
  have h (q : ℝ) : q ∈ interior (integrableExpSet X μ) := by
    rw [all_real_tilts hX hb]
    exact Set.mem_univ _
  have h1 (q : ℝ) : deriv (cgf X μ) q = tiltRaw X μ 1 q := by
    rw [deriv_cgf (h q)]
    simp [tiltRaw]
  have h2 : iteratedDeriv 2 (cgf X μ) =
      fun q ↦ tiltRaw X μ 2 q - (tiltRaw X μ 1 q)^2 := by
    funext q
    rw [iteratedDeriv_two_cgf (h q), h1 q]
    rfl
  have hd2 := (deriv_tiltRaw h 2 t).sub ((deriv_tiltRaw h 1 t).pow 2)
  have h3 : iteratedDeriv 3 (cgf X μ) t =
      tiltRaw X μ 3 t - 3 * tiltRaw X μ 2 t * tiltRaw X μ 1 t +
        2 * (tiltRaw X μ 1 t)^3 := by
    have hd2' : deriv (fun q ↦ tiltRaw X μ 2 q - (tiltRaw X μ 1 q)^2) t = _ := hd2.deriv
    rw [show (3 : ℕ) = 2+1 by rfl, iteratedDeriv_succ, h2, hd2']
    norm_num
    ring
  rw [h3, ← h1 t]
  let ν := μ.tilted (t * X ·)
  let a := deriv (cgf X μ) t
  haveI : IsProbabilityMeasure ν := isProbabilityMeasure_tilted
    (integrable_of_mem_integrableExpSet (interior_subset (h t)))
  have hmean : ∫ x, X x ∂ν = a := integral_tilted_mul_self (h t)
  have hI1 : Integrable X ν := (memLp_tilted_mul (h t) 1).integrable (by norm_num)
  have hI2 : Integrable (fun x ↦ X x ^ 2) ν := by
    have hmem : MemLp X (2 : ℕ) ν := by simpa using memLp_tilted_mul (h t) 2
    exact hmem.integrable_sq
  have hI3 : Integrable (fun x ↦ X x ^ 3) ν := by
    have hmem : MemLp X (3 : ℕ) ν := by simpa using memLp_tilted_mul (h t) 3
    have h := hmem.integrable_norm_pow'
    apply h.mono' ((hX.aestronglyMeasurable.mono_ac (tilted_absolutelyContinuous _ _)).pow 3)
    exact ae_of_all _ (fun x ↦ by
      change |X x ^ 3| ≤ ‖X x‖ ^ 3
      simp only [Real.norm_eq_abs, abs_pow]
      rfl)
  have hexpand : (fun x ↦ (X x-a)^3) =
      (fun x ↦ (X x ^ 3 - (3*a)*X x^2 + (3*a^2)*X x) - a^3) := by
    funext x; ring
  change tiltRaw X μ 3 t - 3 * tiltRaw X μ 2 t * a + 2*a^3 = ∫ x, (X x-a)^3 ∂ν
  rw [tiltRaw_eq, tiltRaw_eq, hexpand]
  let u₃ : Ω → ℝ := fun x ↦ X x ^ 3
  let u₂ : Ω → ℝ := fun x ↦ 3*a*X x^2
  let u₁ : Ω → ℝ := fun x ↦ 3*a^2*X x
  let u₀ : Ω → ℝ := fun _ ↦ a^3
  have hu₃ : Integrable u₃ ν := hI3
  have hu₂ : Integrable u₂ ν := hI2.const_mul _
  have hu₁ : Integrable u₁ ν := hI1.const_mul _
  have hu₀ : Integrable u₀ ν := integrable_const _
  change (∫ x, X x^3 ∂ν) - 3 * (∫ x, X x^2 ∂ν) * a + 2*a^3 =
    ∫ x, (u₃ - u₂ + u₁ - u₀) x ∂ν
  have e₀ : (∫ x, (u₃-u₂+u₁-u₀) x ∂ν) =
      (∫ x, (u₃-u₂+u₁) x ∂ν) - ∫ x, u₀ x ∂ν :=
    integral_sub ((hu₃.sub hu₂).add hu₁) hu₀
  have e₁ : (∫ x, (u₃-u₂+u₁) x ∂ν) =
      (∫ x, (u₃-u₂) x ∂ν) + ∫ x, u₁ x ∂ν :=
    integral_add (hu₃.sub hu₂) hu₁
  have e₂ : (∫ x, (u₃-u₂) x ∂ν) =
      (∫ x, u₃ x ∂ν) - ∫ x, u₂ x ∂ν := integral_sub hu₃ hu₂
  rw [e₀,e₁,e₂]
  simp only [u₀,u₁,u₂,u₃, integral_const_mul, hmean, integral_const, probReal_univ, one_smul]
  ring

theorem abs_third_cgf_le (b : ℝ) (hb0 : 0 ≤ b)
    (hX : AEMeasurable X μ) (hb : ∀ᵐ x ∂μ, |X x| ≤ b) (t : ℝ) :
    |iteratedDeriv 3 (cgf X μ) t| ≤ 8 * b ^ 3 := by
  rw [third_cgf_central_cube b hX hb]
  calc
    _ ≤ ∫ x, |(X x - deriv (cgf X μ) t)^3| ∂(μ.tilted (t * X ·)) := abs_integral_le_integral_abs
    _ ≤ _ := by simp only [abs_pow]; exact tilted_third_abs_moment hX hb0 hb t

end CubeMD
#print axioms CubeMD.third_cgf_central_cube
#print axioms CubeMD.abs_third_cgf_le
