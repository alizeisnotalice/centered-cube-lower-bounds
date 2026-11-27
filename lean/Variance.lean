/-
The variance identity of the `√n/log n` manuscript, eq. (3.2).

For `S_t(x) = ∑_{l<K} ε_l (-1)^{K+l} sin(2πt(1+l/K)) cos(2π(K+l)x)` the manuscript
computes

  `V_K(t) = ∫₀¹ S_t(x)² dx = ½ ∑_{l<K} sin²(2πt(1 + l/K))`,

the cross terms vanishing by the orthogonality `∫₀¹ cos(2πmx)cos(2πnx) = ½δ_{mn}`
proved in `Trig`.

This file proves the underlying computation for an arbitrary cosine series with
positive integer frequencies `M, M+1, …`, then instantiates it.
-/
import Abel
import Trig
import RhoNormalise

open MeasureTheory intervalIntegral Finset
open scoped BigOperators

namespace CenteredCube
namespace RudinDensity

/-- **Variance of a cosine series.**  For `M > 0` and any coefficients `a`,

`∫₀¹ (∑_{l<N} a_l cos(2π(M+l)x))² dx = ½ ∑_{l<N} a_l²`.

All frequencies are distinct positive integers, so only the diagonal contributes. -/
theorem integral_cos_series_sq {N M : ℕ} (hM : 0 < M) (a : ℕ → ℝ) :
    ∫ x in (0 : ℝ)..1,
        (∑ l ∈ range N, a l * Real.cos (((M + l : ℕ) : ℝ) * (2 * Real.pi) * x)) ^ 2
      = 1 / 2 * ∑ l ∈ range N, (a l) ^ 2 := by
  have hpt : ∀ x : ℝ,
      (∑ l ∈ range N, a l * Real.cos (((M + l : ℕ) : ℝ) * (2 * Real.pi) * x)) ^ 2
        = ∑ l ∈ range N, ∑ m ∈ range N,
            (a l * a m) * (Real.cos (((M + l : ℕ) : ℝ) * (2 * Real.pi) * x)
              * Real.cos (((M + m : ℕ) : ℝ) * (2 * Real.pi) * x)) := by
    intro x
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun m _ => ?_))
    ring
  have hcont : ∀ l : ℕ, Continuous fun x : ℝ => ∑ m ∈ range N,
      (a l * a m) * (Real.cos (((M + l : ℕ) : ℝ) * (2 * Real.pi) * x)
        * Real.cos (((M + m : ℕ) : ℝ) * (2 * Real.pi) * x)) := by
    intro l
    refine continuous_finset_sum_interval _ (fun m _ => ?_)
    fun_prop
  have hcont2 : ∀ l m : ℕ, Continuous fun x : ℝ =>
      (a l * a m) * (Real.cos (((M + l : ℕ) : ℝ) * (2 * Real.pi) * x)
        * Real.cos (((M + m : ℕ) : ℝ) * (2 * Real.pi) * x)) := by
    intro l m
    fun_prop
  simp only [hpt]
  rw [intervalIntegral.integral_finsetSum (fun l _ => (hcont l).intervalIntegrable 0 1)]
  have hinner : ∀ l ∈ range N,
      ∑ m ∈ range N, ∫ x in (0 : ℝ)..1,
          (a l * a m) * (Real.cos (((M + l : ℕ) : ℝ) * (2 * Real.pi) * x)
            * Real.cos (((M + m : ℕ) : ℝ) * (2 * Real.pi) * x))
        = a l * a l * (1 / 2) := by
    intro l hl
    have hsingle := Finset.sum_eq_single (s := range N)
      (f := fun m => ∫ x in (0 : ℝ)..1,
        (a l * a m) * (Real.cos (((M + l : ℕ) : ℝ) * (2 * Real.pi) * x)
          * Real.cos (((M + m : ℕ) : ℝ) * (2 * Real.pi) * x))) l ?_ ?_
    · rw [hsingle]
      rw [intervalIntegral.integral_const_mul]
      have hdiag : (∫ x in (0 : ℝ)..1,
          Real.cos (((M + l : ℕ) : ℝ) * (2 * Real.pi) * x)
            * Real.cos (((M + l : ℕ) : ℝ) * (2 * Real.pi) * x)) = 1 / 2 := by
        rw [Trig.integral_cos_mul_cos_two_pi (by omega) (by omega), if_pos rfl]
      rw [hdiag]
    · intro m _ hml
      rw [intervalIntegral.integral_const_mul]
      have hzero : (∫ x in (0 : ℝ)..1,
          Real.cos (((M + l : ℕ) : ℝ) * (2 * Real.pi) * x)
            * Real.cos (((M + m : ℕ) : ℝ) * (2 * Real.pi) * x)) = 0 := by
        rw [Trig.integral_cos_mul_cos_two_pi (by omega) (by omega)]
        rw [if_neg (by omega : (M + l) ≠ (M + m))]
      rw [hzero, mul_zero]
    · intro hlnot
      exact absurd hl hlnot
  have hstep : ∀ i ∈ range N,
      ∫ x in (0 : ℝ)..1, ∑ m ∈ range N,
          (a i * a m) * (Real.cos (((M + i : ℕ) : ℝ) * (2 * Real.pi) * x)
            * Real.cos (((M + m : ℕ) : ℝ) * (2 * Real.pi) * x))
        = a i * a i * (1 / 2) := by
    intro i hi
    rw [intervalIntegral.integral_finsetSum (fun m _ => (hcont2 i m).intervalIntegrable 0 1)]
    exact hinner i hi
  rw [Finset.sum_congr rfl hstep]
  rw [show (∑ x ∈ range N, a x * a x * (1 / 2)) = ∑ x ∈ range N, 1 / 2 * (a x) ^ 2 from
    Finset.sum_congr rfl (fun x _ => by ring)]
  rw [← Finset.mul_sum]


/-- **Covariance of two cosine series.**  For `M > 0` and coefficients `a`, `b`,

`∫₀¹ (∑_{l<N} a_l cos(2π(M+l)x)) (∑_{l<N} b_l cos(2π(M+l)x)) dx = ½ ∑_{l<N} a_l b_l`.

This is `integral_cos_series_sq` with two different coefficient sequences; it is the
engine for the scale covariance `κ_K(t,s) = E[Y_t Y_s]` of the manuscript. -/
theorem integral_cos_series_mul {N M : ℕ} (hM : 0 < M) (a b : ℕ → ℝ) :
    ∫ x in (0 : ℝ)..1,
        (∑ l ∈ range N, a l * Real.cos (((M + l : ℕ) : ℝ) * (2 * Real.pi) * x))
          * (∑ l ∈ range N, b l * Real.cos (((M + l : ℕ) : ℝ) * (2 * Real.pi) * x))
      = 1 / 2 * ∑ l ∈ range N, a l * b l := by
  have hpt : ∀ x : ℝ,
      (∑ l ∈ range N, a l * Real.cos (((M + l : ℕ) : ℝ) * (2 * Real.pi) * x))
          * (∑ l ∈ range N, b l * Real.cos (((M + l : ℕ) : ℝ) * (2 * Real.pi) * x))
        = ∑ l ∈ range N, ∑ m ∈ range N,
            (a l * b m) * (Real.cos (((M + l : ℕ) : ℝ) * (2 * Real.pi) * x)
              * Real.cos (((M + m : ℕ) : ℝ) * (2 * Real.pi) * x)) := by
    intro x
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun m _ => ?_))
    ring
  have hcont : ∀ l : ℕ, Continuous fun x : ℝ => ∑ m ∈ range N,
      (a l * b m) * (Real.cos (((M + l : ℕ) : ℝ) * (2 * Real.pi) * x)
        * Real.cos (((M + m : ℕ) : ℝ) * (2 * Real.pi) * x)) := by
    intro l
    refine continuous_finset_sum_interval _ (fun m _ => ?_)
    fun_prop
  have hcont2 : ∀ l m : ℕ, Continuous fun x : ℝ =>
      (a l * b m) * (Real.cos (((M + l : ℕ) : ℝ) * (2 * Real.pi) * x)
        * Real.cos (((M + m : ℕ) : ℝ) * (2 * Real.pi) * x)) := by
    intro l m
    fun_prop
  simp only [hpt]
  rw [intervalIntegral.integral_finsetSum (fun l _ => (hcont l).intervalIntegrable 0 1)]
  have hinner : ∀ l ∈ range N,
      ∑ m ∈ range N, ∫ x in (0 : ℝ)..1,
          (a l * b m) * (Real.cos (((M + l : ℕ) : ℝ) * (2 * Real.pi) * x)
            * Real.cos (((M + m : ℕ) : ℝ) * (2 * Real.pi) * x))
        = a l * b l * (1 / 2) := by
    intro l hl
    have hsingle := Finset.sum_eq_single (s := range N)
      (f := fun m => ∫ x in (0 : ℝ)..1,
        (a l * b m) * (Real.cos (((M + l : ℕ) : ℝ) * (2 * Real.pi) * x)
          * Real.cos (((M + m : ℕ) : ℝ) * (2 * Real.pi) * x))) l ?_ ?_
    · rw [hsingle]
      rw [intervalIntegral.integral_const_mul]
      have hdiag : (∫ x in (0 : ℝ)..1,
          Real.cos (((M + l : ℕ) : ℝ) * (2 * Real.pi) * x)
            * Real.cos (((M + l : ℕ) : ℝ) * (2 * Real.pi) * x)) = 1 / 2 := by
        rw [Trig.integral_cos_mul_cos_two_pi (by omega) (by omega), if_pos rfl]
      rw [hdiag]
    · intro m _ hml
      rw [intervalIntegral.integral_const_mul]
      have hzero : (∫ x in (0 : ℝ)..1,
          Real.cos (((M + l : ℕ) : ℝ) * (2 * Real.pi) * x)
            * Real.cos (((M + m : ℕ) : ℝ) * (2 * Real.pi) * x)) = 0 := by
        rw [Trig.integral_cos_mul_cos_two_pi (by omega) (by omega)]
        rw [if_neg (by omega : (M + l) ≠ (M + m))]
      rw [hzero, mul_zero]
    · intro hlnot
      exact absurd hl hlnot
  have hstep : ∀ i ∈ range N,
      ∫ x in (0 : ℝ)..1, ∑ m ∈ range N,
          (a i * b m) * (Real.cos (((M + i : ℕ) : ℝ) * (2 * Real.pi) * x)
            * Real.cos (((M + m : ℕ) : ℝ) * (2 * Real.pi) * x))
        = a i * b i * (1 / 2) := by
    intro i hi
    rw [intervalIntegral.integral_finsetSum (fun m _ => (hcont2 i m).intervalIntegrable 0 1)]
    exact hinner i hi
  rw [Finset.sum_congr rfl hstep]
  rw [show (∑ x ∈ range N, a x * b x * (1 / 2)) = ∑ x ∈ range N, 1 / 2 * (a x * b x) from
    Finset.sum_congr rfl (fun x _ => by ring)]
  rw [← Finset.mul_sum]

/-- The manuscript's cosine series `S_t`, with the Rudin–Shapiro signs and the
alternating factor `(-1)^{K+l}`. -/
noncomputable def Sfun (K : ℕ) (t x : ℝ) : ℝ :=
  ∑ l ∈ range K,
    ((coef K l).1.re * (-1 : ℝ) ^ (K + l) * Real.sin (2 * Real.pi * t * (1 + (l : ℝ) / (K : ℝ))))
      * Real.cos (((K + l : ℕ) : ℝ) * (2 * Real.pi) * x)

/-- **Mean zero**: `E S_t(U) = 0`, i.e. `∫₀¹ S_t = 0`. -/
theorem integral_Sfun (K : ℕ) (hK : 1 ≤ K) (t : ℝ) :
    ∫ x in (0 : ℝ)..1, Sfun K t x = 0 := by
  rw [show Sfun K t = fun x => ∑ l ∈ range K,
    ((coef K l).1.re * (-1 : ℝ) ^ (K + l) * Real.sin (2 * Real.pi * t * (1 + (l : ℝ) / (K : ℝ))))
      * Real.cos (((K + l : ℕ) : ℝ) * (2 * Real.pi) * x) from rfl]
  rw [intervalIntegral.integral_finsetSum (fun l _ => ?_)]
  · refine Finset.sum_eq_zero (fun l hl => ?_)
    rw [intervalIntegral.integral_const_mul]
    have hcast : ((((K + l : ℕ)) : ℤ) : ℝ) = ((K + l : ℕ) : ℝ) := by push_cast; ring
    rw [← hcast, Trig.integral_cos_two_pi_mul_int (((K + l : ℕ)) : ℤ)]
    rw [if_neg (by omega : ¬ (((K + l : ℕ)) : ℤ) = 0)]
    ring
  · have : Continuous fun x : ℝ =>
        ((coef K l).1.re * (-1 : ℝ) ^ (K + l) * Real.sin (2 * Real.pi * t * (1 + (l : ℝ) / (K : ℝ))))
          * Real.cos (((K + l : ℕ) : ℝ) * (2 * Real.pi) * x) := by fun_prop
    exact this.intervalIntegrable 0 1

/-- **The variance identity**: `V_K(t) = ½ ∑_{l<K} sin²(2πt(1 + l/K))`. -/
theorem integral_Sfun_sq (K : ℕ) (hK : 1 ≤ K) (t : ℝ) :
    ∫ x in (0 : ℝ)..1, (Sfun K t x) ^ 2
      = 1 / 2 * ∑ l ∈ range K,
          (Real.sin (2 * Real.pi * t * (1 + (l : ℝ) / (K : ℝ)))) ^ 2 := by
  have hmain := integral_cos_series_sq (N := K) (M := K) (by omega)
    (a := fun l => (coef K l).1.re * (-1 : ℝ) ^ (K + l)
      * Real.sin (2 * Real.pi * t * (1 + (l : ℝ) / (K : ℝ))))
  rw [show Sfun K t = fun x => ∑ l ∈ range K,
    ((coef K l).1.re * (-1 : ℝ) ^ (K + l) * Real.sin (2 * Real.pi * t * (1 + (l : ℝ) / (K : ℝ))))
      * Real.cos (((K + l : ℕ) : ℝ) * (2 * Real.pi) * x) from rfl, hmain]
  congr 1
  refine Finset.sum_congr rfl (fun l hl => ?_)
  have hK2 : l < 2 ^ K := lt_of_lt_of_le (Finset.mem_range.mp hl) (le_two_pow_self K)
  have hc := (coef_unit K l hK2).1
  have heps : ((coef K l).1.re) ^ 2 = 1 := by
    rcases hc with h | h <;> simp [h]
  have hsign : ((-1 : ℝ) ^ (K + l)) ^ 2 = 1 := by
    rw [sq, ← pow_add]
    exact Even.neg_one_pow ⟨K + l, by ring⟩
  calc ((coef K l).1.re * (-1 : ℝ) ^ (K + l)
        * Real.sin (2 * Real.pi * t * (1 + (l : ℝ) / (K : ℝ)))) ^ 2
      = ((coef K l).1.re) ^ 2 * ((-1 : ℝ) ^ (K + l)) ^ 2
        * (Real.sin (2 * Real.pi * t * (1 + (l : ℝ) / (K : ℝ)))) ^ 2 := by ring
    _ = (Real.sin (2 * Real.pi * t * (1 + (l : ℝ) / (K : ℝ)))) ^ 2 := by
      rw [heps, hsign]; ring


/-- **Scaling step of `σ_t²`.**  If the normalised average is `S_t / c` with
`c = 30πK^{3/2} r(t)`, then its `L²` norm is `V_K(t)/c²`; with `c² = 900π²K³r(t)²`
this is the manuscript's `σ_t² = V_K(t)/(900π²K³r(t)²)`.

The identification `d_t = S_t/(30πK^{3/2}r(t))` itself is eq. (3.1) of the
manuscript (the exact one-dimensional average) and is *not* proved here. -/
theorem integral_scaled_sq (K : ℕ) (hK : 1 ≤ K) (t : ℝ) {c : ℝ} (hc : c ≠ 0) :
    ∫ x in (0 : ℝ)..1, (Sfun K t x / c) ^ 2
      = (1 / 2 * ∑ l ∈ range K,
          (Real.sin (2 * Real.pi * t * (1 + (l : ℝ) / (K : ℝ)))) ^ 2) / c ^ 2 := by
  have hcont : Continuous fun x : ℝ => (Sfun K t x) ^ 2 := by
    unfold Sfun
    fun_prop
  have hdiv : ∫ x in (0 : ℝ)..1, (Sfun K t x / c) ^ 2
      = (∫ x in (0 : ℝ)..1, (Sfun K t x) ^ 2) / c ^ 2 := by
    rw [show (fun x => (Sfun K t x / c) ^ 2) = fun x => (Sfun K t x) ^ 2 / c ^ 2 from by
      funext x; ring]
    rw [intervalIntegral.integral_div]
  rw [hdiv, integral_Sfun_sq K hK t]


/-- **The scale covariance of the manuscript**: `∫₀¹ S_t S_s = ½ ∑_{l<K} sin_t(l) sin_s(l)`,
with `sin_t(l) = sin(2πt(1+l/K))`.  The signs `ε_l` and `(-1)^{K+l}` disappear because
they are `±1`. -/
theorem integral_Sfun_mul {K : ℕ} (hK : 1 ≤ K) (t s : ℝ) :
    ∫ x in (0 : ℝ)..1, Sfun K t x * Sfun K s x
      = 1 / 2 * ∑ l ∈ range K,
          (Real.sin (2 * Real.pi * t * (1 + (l : ℝ) / (K : ℝ))))
            * (Real.sin (2 * Real.pi * s * (1 + (l : ℝ) / (K : ℝ)))) := by
  have hmain := integral_cos_series_mul (N := K) (M := K) (by omega)
    (a := fun l => (coef K l).1.re * (-1 : ℝ) ^ (K + l)
      * Real.sin (2 * Real.pi * t * (1 + (l : ℝ) / (K : ℝ))))
    (b := fun l => (coef K l).1.re * (-1 : ℝ) ^ (K + l)
      * Real.sin (2 * Real.pi * s * (1 + (l : ℝ) / (K : ℝ))))
  rw [show Sfun K t = fun x => ∑ l ∈ range K,
    ((coef K l).1.re * (-1 : ℝ) ^ (K + l) * Real.sin (2 * Real.pi * t * (1 + (l : ℝ) / (K : ℝ))))
      * Real.cos (((K + l : ℕ) : ℝ) * (2 * Real.pi) * x) from rfl,
    show Sfun K s = fun x => ∑ l ∈ range K,
    ((coef K l).1.re * (-1 : ℝ) ^ (K + l) * Real.sin (2 * Real.pi * s * (1 + (l : ℝ) / (K : ℝ))))
      * Real.cos (((K + l : ℕ) : ℝ) * (2 * Real.pi) * x) from rfl, hmain]
  congr 1
  refine Finset.sum_congr rfl (fun l hl => ?_)
  have hK2 : l < 2 ^ K := lt_of_lt_of_le (Finset.mem_range.mp hl) (le_two_pow_self K)
  have hc := (coef_unit K l hK2).1
  have heps : ((coef K l).1.re) ^ 2 = 1 := by
    rcases hc with h | h <;> simp [h]
  have hsign : ((-1 : ℝ) ^ (K + l)) ^ 2 = 1 := by
    rw [sq, ← pow_add]
    exact Even.neg_one_pow ⟨K + l, by ring⟩
  calc ((coef K l).1.re * (-1 : ℝ) ^ (K + l)
        * Real.sin (2 * Real.pi * t * (1 + (l : ℝ) / (K : ℝ))))
      * ((coef K l).1.re * (-1 : ℝ) ^ (K + l)
        * Real.sin (2 * Real.pi * s * (1 + (l : ℝ) / (K : ℝ))))
      = ((coef K l).1.re) ^ 2 * ((-1 : ℝ) ^ (K + l)) ^ 2
        * (Real.sin (2 * Real.pi * t * (1 + (l : ℝ) / (K : ℝ)))
          * Real.sin (2 * Real.pi * s * (1 + (l : ℝ) / (K : ℝ)))) := by ring
    _ = Real.sin (2 * Real.pi * t * (1 + (l : ℝ) / (K : ℝ)))
          * Real.sin (2 * Real.pi * s * (1 + (l : ℝ) / (K : ℝ))) := by
      rw [heps, hsign]; ring

end RudinDensity
end CenteredCube

#print axioms CenteredCube.RudinDensity.integral_cos_series_sq
#print axioms CenteredCube.RudinDensity.integral_cos_series_mul
#print axioms CenteredCube.RudinDensity.integral_Sfun
#print axioms CenteredCube.RudinDensity.integral_Sfun_sq
#print axioms CenteredCube.RudinDensity.integral_scaled_sq
#print axioms CenteredCube.RudinDensity.integral_Sfun_mul
