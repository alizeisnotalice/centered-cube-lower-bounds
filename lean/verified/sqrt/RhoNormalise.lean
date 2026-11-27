/-
Normalisation of the Rudin–Shapiro density: `∫₀¹ ρ_K = 1`.

This completes Lemma 2.3 of the `√n/log n` manuscript, whose first two conclusions
(the `15√K` weighted bound and `1/2 ≤ ρ_K ≤ 3/2`) are in `Abel.lean`.

The argument is the manuscript's: every frequency of `ρ_K` is one of the positive
integers `K + l`, so every term has mean zero over a period.
-/
import Abel
import Trig
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open MeasureTheory intervalIntegral Finset
open scoped BigOperators

namespace CenteredCube
namespace RudinDensity

/-- `∫₀¹ e^{2πimx} dx = 0` for every positive integer `m`. -/
theorem integral_exp_period (m : ℕ) (hm : 1 ≤ m) :
    ∫ x in (0 : ℝ)..1, Complex.exp (((m : ℂ) * (2 * Real.pi) * Complex.I) * x) = 0 := by
  have hm' : (m : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.pos_iff_ne_zero.mp (by omega) : m ≠ 0)
  have hpi : ((2 : ℂ) * Real.pi) ≠ 0 := by
    have : (2 : ℝ) * Real.pi ≠ 0 := by positivity
    exact_mod_cast this
  have hc : ((m : ℂ) * (2 * Real.pi) * Complex.I) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hm' hpi) Complex.I_ne_zero
  rw [integral_exp_mul_complex hc]
  have hone : Complex.exp ((m : ℂ) * (2 * Real.pi) * Complex.I) = 1 := by
    rw [show ((m : ℂ) * (2 * Real.pi) * Complex.I)
        = (m : ℂ) * (2 * Real.pi * Complex.I) by ring, Complex.exp_nat_mul]
    rw [show (2 * (Real.pi : ℂ) * Complex.I) = ((2 * Real.pi : ℝ) : ℂ) * Complex.I by
      push_cast; ring, Complex.exp_ofReal_mul_I]
    simp [Real.cos_two_pi, Real.sin_two_pi]
  simp only [Complex.ofReal_one, Complex.ofReal_zero, mul_one, mul_zero,
    Complex.exp_zero]
  rw [hone, sub_self, zero_div]

/-- `∫₀¹ (e^{2πix})^m dx = 0` for `m ≥ 1`. -/
theorem integral_zof_pow (m : ℕ) (hm : 1 ≤ m) :
    ∫ x in (0 : ℝ)..1, (zof x) ^ m = 0 := by
  have hpt : ∀ x : ℝ, (zof x) ^ m
      = Complex.exp (((m : ℂ) * (2 * Real.pi) * Complex.I) * x) := by
    intro x
    rw [zof, ← Complex.exp_nat_mul]
    congr 1
    ring
  simp only [hpt]
  exact integral_exp_period m hm

/-- Continuity of a finite sum of continuous functions. -/
theorem continuous_finset_sum_interval {ι E : Type*} [AddCommMonoid E] [TopologicalSpace E]
    [ContinuousAdd E] (s : Finset ι) {f : ι → ℝ → E}
    (hf : ∀ i ∈ s, Continuous (f i)) :
    Continuous fun x => ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using continuous_const (y := (0 : E))
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

/-- `∫₀¹ Re(A e^{2πinx}) dx = 0` for `n ≥ 1` and every constant `A`. -/
theorem integral_re_mul_zof_pow (A : ℂ) (n : ℕ) (hn : 1 ≤ n) :
    ∫ x in (0 : ℝ)..1, Complex.re (A * (zof x) ^ n) = 0 := by
  have hpow : ∀ x : ℝ, (zof x) ^ n
      = ((Real.cos ((n : ℝ) * (2 * Real.pi) * x) : ℂ)
        + (Real.sin ((n : ℝ) * (2 * Real.pi) * x) : ℂ) * Complex.I) := by
    intro x
    rw [zof, ← Complex.exp_nat_mul]
    rw [show (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I * (x : ℂ))
        = (((n : ℝ) * (2 * Real.pi) * x : ℝ) : ℂ) * Complex.I by push_cast; ring]
    rw [Complex.exp_ofReal_mul_I]
  have hre : ∀ x : ℝ, Complex.re (A * (zof x) ^ n)
      = A.re * Real.cos ((n : ℝ) * (2 * Real.pi) * x)
        - A.im * Real.sin ((n : ℝ) * (2 * Real.pi) * x) := by
    intro x
    rw [hpow x, Complex.mul_re]
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.cos_ofReal_re, Complex.sin_ofReal_re, Complex.cos_ofReal_im,
      Complex.sin_ofReal_im, mul_zero, mul_one, sub_zero, add_zero]
    ring
  simp only [hre]
  have hcont1 : Continuous fun x : ℝ => A.re * Real.cos ((n : ℝ) * (2 * Real.pi) * x) := by
    fun_prop
  have hcont2 : Continuous fun x : ℝ => A.im * Real.sin ((n : ℝ) * (2 * Real.pi) * x) := by
    fun_prop
  rw [intervalIntegral.integral_sub (hcont1.intervalIntegrable 0 1)
    (hcont2.intervalIntegrable 0 1)]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have hcast : (((n : ℤ)) : ℝ) = (n : ℝ) := by push_cast; ring
  rw [← hcast, Trig.integral_cos_two_pi_mul_int (n : ℤ),
    Trig.integral_sin_two_pi_mul_int (n : ℤ)]
  have hn0 : ((n : ℤ)) ≠ 0 := by exact_mod_cast (Nat.pos_iff_ne_zero.mp (by omega))
  rw [if_neg hn0]
  ring


/-- The real part of a finite sum of complex numbers. -/
theorem re_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    Complex.re (∑ i ∈ s, f i) = ∑ i ∈ s, Complex.re (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Complex.add_re, ih]

/-- **`∫₀¹ ρ_K dx = 1`** — the third conclusion of the manuscript's Lemma 2.3. -/
theorem integral_rho (K : ℕ) (hK : 1 ≤ K) :
    ∫ x in (0 : ℝ)..1, rho K x = 1 := by
  let F : ℝ → ℝ := fun x => ∑ l ∈ range K,
    Complex.re ((((1 : ℂ) + (l : ℂ) / (K : ℂ)) * (coef K l).1) * (zof x) ^ (K + l))
  have hseries : ∀ x : ℝ, (zof x) ^ K * weightedSum (zof x) K
      = ∑ l ∈ range K, (((1 : ℂ) + (l : ℂ) / (K : ℂ)) * (coef K l).1) * (zof x) ^ (K + l) := by
    intro x
    rw [weightedSum_eq_series hK (zof x), Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [pow_add]
    ring
  have hcont : ∀ l : ℕ, Continuous fun x : ℝ =>
      Complex.re ((((1 : ℂ) + (l : ℂ) / (K : ℂ)) * (coef K l).1) * (zof x) ^ (K + l)) := by
    intro l
    unfold zof
    fun_prop
  have hFcont : Continuous F := by
    dsimp only [F]
    exact continuous_finset_sum_interval _ (fun l _ => hcont l)
  have hpt : ∀ x : ℝ, rho K x = 1 + (1 / (30 * Real.sqrt (K : ℝ))) * F x := by
    intro x
    dsimp only [F]
    rw [rho, hseries x, re_finset_sum]
  have hfun : rho K = fun x => (1 : ℝ) + (1 / (30 * Real.sqrt (K : ℝ))) * F x := funext hpt
  have hzero : ∫ x in (0 : ℝ)..1, F x = 0 := by
    dsimp only [F]
    rw [intervalIntegral.integral_finsetSum (fun l _ => (hcont l).intervalIntegrable 0 1)]
    exact Finset.sum_eq_zero (fun l _ => integral_re_mul_zof_pow _ (K + l) (by omega))
  rw [hfun, intervalIntegral.integral_add intervalIntegrable_const
    ((hFcont.const_mul _).intervalIntegrable 0 1)]
  rw [intervalIntegral.integral_const, intervalIntegral.integral_const_mul, hzero]
  norm_num

end RudinDensity
end CenteredCube

#print axioms CenteredCube.RudinDensity.integral_exp_period
#print axioms CenteredCube.RudinDensity.integral_zof_pow
#print axioms CenteredCube.RudinDensity.integral_re_mul_zof_pow
#print axioms CenteredCube.RudinDensity.integral_rho
