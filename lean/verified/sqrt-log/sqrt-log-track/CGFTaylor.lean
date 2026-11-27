import CGFThird
open MeasureTheory ProbabilityTheory Set
namespace CubeMD

private theorem taylor_quadratic_abs_bound (f : ℝ → ℝ)
    (hf : ContDiff ℝ ⊤ f) (t C : ℝ) (ht : 0 ≤ t) (hC : 0 ≤ C)
    (h3 : ∀ x, |iteratedDeriv 3 f x| ≤ C) :
    |f t - (f 0 + t * deriv f 0 + t^2 / 2 * iteratedDeriv 2 f 0)| ≤ C * t^3 / 6 := by
  rcases ht.eq_or_lt with rfl | hp
  · simp
  have hs : (uIcc (0 : ℝ) t) = Icc 0 t := uIcc_of_le hp.le
  have hu : UniqueDiffOn ℝ (uIcc (0 : ℝ) t) := uniqueDiffOn_uIcc hp.ne
  have h0 : 0 ∈ uIcc (0 : ℝ) t := left_mem_uIcc
  obtain ⟨s, hsm, hRem⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (n := 2) (x₀ := 0) (x := t) hp.ne
      (hf.contDiffOn.of_le (by simp))
  have hid (k : ℕ) :
      iteratedDerivWithin k f (uIcc 0 t) 0 = iteratedDeriv k f 0 :=
    iteratedDerivWithin_eq_iteratedDeriv hu (hf.contDiffAt.of_le (by simp)) h0
  have hTaylor :
      taylorWithinEval f 2 (uIcc 0 t) 0 t = f 0 + t * deriv f 0 + t^2 / 2 * iteratedDeriv 2 f 0 := by
    rw [taylorWithinEval_succ f 1 (uIcc 0 t) 0 t,
        taylorWithinEval_succ f 0 (uIcc 0 t) 0 t]
    norm_num [hid, iteratedDeriv_one, smul_eq_mul] <;> ring_nf <;> simp
  rw [hTaylor, sub_zero] at hRem
  rw [hRem, abs_div, abs_mul, abs_of_nonneg (pow_nonneg ht 3)]
  norm_num
  gcongr
  exact h3 s

private theorem taylor_linear_abs_bound (f : ℝ → ℝ)
    (hf : ContDiff ℝ ⊤ f) (t C : ℝ) (ht : 0 ≤ t) (hC : 0 ≤ C)
    (h2 : ∀ x, |iteratedDeriv 2 f x| ≤ C) :
    |f t - (f 0 + t * deriv f 0)| ≤ C * t^2 / 2 := by
  rcases ht.eq_or_lt with rfl | hp
  · simp
  have hu : UniqueDiffOn ℝ (uIcc (0 : ℝ) t) := uniqueDiffOn_uIcc hp.ne
  have h0 : 0 ∈ uIcc (0 : ℝ) t := left_mem_uIcc
  obtain ⟨s, hsm, hRem⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (n := 1) (x₀ := 0) (x := t) hp.ne (hf.contDiffOn.of_le (by simp))
  have hid : iteratedDerivWithin 1 f (uIcc 0 t) 0 = iteratedDeriv 1 f 0 :=
    iteratedDerivWithin_eq_iteratedDeriv hu (hf.contDiffAt.of_le (by simp)) h0
  have hTaylor : taylorWithinEval f 1 (uIcc 0 t) 0 t = f 0 + t * deriv f 0 := by
    rw [show (1 : ℕ) = 0 + 1 by rfl, taylorWithinEval_succ]
    simp [hid, iteratedDeriv_one, smul_eq_mul]
  rw [hTaylor, sub_zero] at hRem
  rw [hRem, abs_div, abs_mul, abs_of_nonneg (pow_nonneg ht 2)]
  norm_num
  gcongr
  exact h2 s

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {X : Ω → ℝ}

theorem cgf_taylor_bounds (b t : ℝ) (hb0 : 0 ≤ b)
    (hX : AEMeasurable X μ) (hb : ∀ᵐ x ∂μ, |X x| ≤ b)
    (hmean : (∫ x, X x ∂μ) = 0) (hvar : (∫ x, X x^2 ∂μ) = 1) (ht : 0 ≤ t) :
    |iteratedDeriv 2 (cgf X μ) t - 1| ≤ 8 * b^3 * t ∧
    (|deriv (cgf X μ) t - t| ≤ 8*b^3*t^2/2 ∧
    |cgf X μ t - t^2/2| ≤ 8*b^3*t^3/6) := by
  let f := cgf X μ
  let C := 8 * b^3
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hI (q : ℝ) : q ∈ interior (integrableExpSet X μ) := by
    rw [all_real_tilts hX hb]
    exact Set.mem_univ _
  have ha (q : ℝ) : AnalyticAt ℝ f q := analyticAt_cgf (hI q)
  have hf : ContDiff ℝ ⊤ f := contDiff_iff_contDiffAt.mpr fun q ↦ (ha q).contDiffAt
  have hfd (q : ℝ) : AnalyticAt ℝ (deriv f) q := (ha q).deriv
  have hfd' : ContDiff ℝ ⊤ (deriv f) := contDiff_iff_contDiffAt.mpr fun q ↦ (hfd q).contDiffAt
  have hf0 : f 0 = 0 := by simp [f,cgf,mgf]
  have hf1 : deriv f 0 = 0 := by rw [deriv_cgf_zero (hI 0), hmean, zero_div]
  have hf2 : iteratedDeriv 2 f 0 = 1 := by
    change iteratedDeriv 2 (cgf X μ) 0 = 1
    rw [iteratedDeriv_two_cgf (hI 0), hf1]
    simpa [mgf] using hvar
  have hB (q : ℝ) : |iteratedDeriv 3 f q| ≤ C := abs_third_cgf_le b hb0 hX hb q
  have hE2 : iteratedDeriv 2 f = deriv (deriv f) := by
    rw [show (2 : ℕ) = 1 + 1 by rfl, iteratedDeriv_succ, iteratedDeriv_one]
  have hE3 : iteratedDeriv 3 f = deriv (iteratedDeriv 2 f) := by
    rw [show (3 : ℕ) = 2 + 1 by rfl, iteratedDeriv_succ]
  have hE3' : iteratedDeriv 2 (deriv f) = iteratedDeriv 3 f := by
    rw [hE3, hE2, show (2 : ℕ) = 1 + 1 by rfl, iteratedDeriv_succ, iteratedDeriv_one]
  have hfirst : |iteratedDeriv 2 f t - 1| ≤ C*t := by
    rcases ht.eq_or_lt with rfl | hp
    · simp [hf2]
    have hd : Differentiable ℝ (iteratedDeriv 2 f) := by
      rw [hE2]
      exact fun q ↦ (hfd q).deriv.differentiableAt
    obtain ⟨s, hs, he⟩ := exists_deriv_eq_slope _ hp hd.continuous.continuousOn hd.differentiableOn
    have heq : iteratedDeriv 2 f t - 1 = iteratedDeriv 3 f s * t := by
      rw [hE3, he, hf2, sub_zero, div_mul_cancel₀ _ hp.ne']
    rw [heq, abs_mul, abs_of_nonneg ht]
    exact mul_le_mul_of_nonneg_right (hB s) ht
  refine ⟨hfirst, ?_, ?_⟩
  · have hh := taylor_linear_abs_bound _ hfd' t C ht hC
      (fun x ↦ by rw [hE3']; exact hB x)
    rw [← hE2, hf1, hf2, mul_one, zero_add] at hh
    exact hh
  · have hh := taylor_quadratic_abs_bound _ hf t C ht hC hB
    rw [hf0,hf1,hf2,mul_zero,mul_one,zero_add,zero_add] at hh
    exact hh

end CubeMD
#print axioms CubeMD.cgf_taylor_bounds
