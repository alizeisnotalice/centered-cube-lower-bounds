/-
The sup-norm bound of `lem:bounded`: `sup_x |S_t(x)| ≤ 5√K`.

The manuscript expands the sine and cosine of

  `S_t(x) = ∑_{l<K} ε_l (-1)^{K+l} sin(2πt(1+l/K)) cos(2π(K+l)x)`

into exponentials, obtaining four Rudin–Shapiro polynomials evaluated on the unit
circle with outer coefficients of modulus `1/4`, and applies `lem:rudin`
(`|F_K| ≤ 5√K`).  Here the two frequencies are combined with
`sin B cos A = ½(sin(B+A) + sin(B−A))`, giving two polynomials with coefficient
`1/2`, so

  `S_t(x) = ½ (Im E(t/K+x) + Im E(t/K−x))`,  `E(w) = (-1)^K e^{2πiKw} F_K(-e^{2πiw})`,

and `|S_t(x)| ≤ ½(5√K + 5√K) = 5√K`.

Consequently, on the window where `V_K(t) ≥ K/8`, the standardised variable obeys
`‖Y_t‖_∞ = |S_t|/√(V_K(t)) ≤ 5√8` (`abs_Y_le`).
-/
import Center

open Finset
open scoped BigOperators

namespace CenteredCube
namespace RudinDensity

theorem two_mul_sin_mul_cos (A B : ℝ) :
    2 * (Real.sin B * Real.cos A) = Real.sin (B + A) + Real.sin (B - A) := by
  have h1 := Real.sin_add B A
  have h2 := Real.sin_sub B A
  linarith

theorem rsPrefix_eq_sum (K : ℕ) (z : ℂ) :
    rsPrefix z K = ∑ l ∈ range K, (coef K l).1 * z ^ l := by
  induction K with
  | zero => simp [rsPrefix_zero]
  | succ n ih =>
    have hcoef : ∀ x ∈ range n, (coef (n + 1) x).1 = (coef n x).1 := by
      intro x hx
      rw [coef_succ_of_lt (lt_of_lt_of_le (Finset.mem_range.mp hx) (le_two_pow n))]
    have hsum : (∑ x ∈ range n, (coef (n + 1) x).1 * z ^ x)
        = ∑ x ∈ range n, (coef n x).1 * z ^ x :=
      Finset.sum_congr rfl (fun x hx => by rw [hcoef x hx])
    rw [Finset.sum_range_succ, hsum, ← ih,
      ← rsPrefix_eq_coef (K := n + 1) (l := n) (by omega)]
    ring

/-- The complex sum whose imaginary part is the sine series of `S_t`. -/
noncomputable def Sexp (K : ℕ) (w : ℝ) : ℂ :=
  ∑ l ∈ range K, ((coef K l).1.re * (-1 : ℝ) ^ (K + l) : ℂ)
    * Complex.exp (((2 * Real.pi * (((K + l : ℕ)) : ℝ) * w : ℝ) : ℂ) * Complex.I)

/-- `S_t` is the imaginary part of two such sums, at `t/K + x` and `t/K − x`. -/
theorem Sfun_eq_im {K : ℕ} (hK : 1 ≤ K) (t x : ℝ) :
    Sfun K t x = 1 / 2 * ((Sexp K (t / K + x)).im + (Sexp K (t / K - x)).im) := by
  have hK0 : ((K : ℕ) : ℝ) ≠ 0 := by positivity
  have him : ∀ (l : ℕ) (θ : ℝ),
      (((coef K l).1.re * (-1 : ℝ) ^ (K + l) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)).im
        = (coef K l).1.re * (-1 : ℝ) ^ (K + l) * Real.sin θ := by
    intro l θ
    have h : ((coef K l).1.re * (-1 : ℝ) ^ (K + l) : ℂ)
          * Complex.exp ((θ : ℂ) * Complex.I)
        = ↑((coef K l).1.re * (-1 : ℝ) ^ (K + l) * Real.cos θ)
          + ↑((coef K l).1.re * (-1 : ℝ) ^ (K + l) * Real.sin θ) * Complex.I := by
      rw [Complex.exp_ofReal_mul_I]
      push_cast
      ring
    rw [h]
    simp only [Complex.add_im, Complex.mul_im, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_one,
      mul_zero, add_zero, zero_add]
  have hterm : ∀ l ∈ range K,
      2 * (((coef K l).1.re * (-1 : ℝ) ^ (K + l)
          * Real.sin (2 * Real.pi * t * (1 + (l : ℝ) / (K : ℝ))))
        * Real.cos ((((K + l : ℕ)) : ℝ) * (2 * Real.pi) * x))
      = (((coef K l).1.re * (-1 : ℝ) ^ (K + l) : ℂ)
          * Complex.exp (((2 * Real.pi * (((K + l : ℕ)) : ℝ) * (t / (K : ℝ) + x) : ℝ) : ℂ)
            * Complex.I)).im
        + (((coef K l).1.re * (-1 : ℝ) ^ (K + l) : ℂ)
          * Complex.exp (((2 * Real.pi * (((K + l : ℕ)) : ℝ) * (t / (K : ℝ) - x) : ℝ) : ℂ)
            * Complex.I)).im := by
    intro l _
    have harg1 : 2 * Real.pi * t * (1 + (l : ℝ) / (K : ℝ))
          + (((K + l : ℕ)) : ℝ) * (2 * Real.pi) * x
        = 2 * Real.pi * (((K + l : ℕ)) : ℝ) * (t / (K : ℝ) + x) := by
      field_simp
      push_cast
      ring
    have harg2 : 2 * Real.pi * t * (1 + (l : ℝ) / (K : ℝ))
          - (((K + l : ℕ)) : ℝ) * (2 * Real.pi) * x
        = 2 * Real.pi * (((K + l : ℕ)) : ℝ) * (t / (K : ℝ) - x) := by
      field_simp
      push_cast
      ring
    rw [him l, him l, ← harg1, ← harg2]
    have hs := two_mul_sin_mul_cos ((((K + l : ℕ)) : ℝ) * (2 * Real.pi) * x)
      (2 * Real.pi * t * (1 + (l : ℝ) / (K : ℝ)))
    linear_combination ((coef K l).1.re * (-1 : ℝ) ^ (K + l)) * hs
  rw [Sfun, Sexp, Sexp, Complex.im_sum, Complex.im_sum, ← Finset.sum_add_distrib,
    Finset.mul_sum]
  refine Finset.sum_congr rfl (fun l hl => ?_)
  have h := hterm l hl
  linear_combination (1 / 2 : ℝ) * h


/-- The geometric form of `Sexp`: `(-1)^K e^{2πiKw} F_K(-e^{2πiw})`. -/
theorem Sexp_eq {K : ℕ} (w : ℝ) :
    Sexp K w = (-1 : ℂ) ^ K
        * Complex.exp (((2 * Real.pi * (K : ℝ) * w : ℝ) : ℂ) * Complex.I)
        * rsPrefix (-(Complex.exp (((2 * Real.pi * w : ℝ) : ℂ) * Complex.I))) K := by
  rw [Sexp, rsPrefix_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun l hl => ?_)
  have hK2 : l < 2 ^ K := lt_of_lt_of_le (Finset.mem_range.mp hl) (le_two_pow K)
  have hexp : Complex.exp (((2 * Real.pi * (((K + l : ℕ)) : ℝ) * w : ℝ) : ℂ) * Complex.I)
      = Complex.exp (((2 * Real.pi * (K : ℝ) * w : ℝ) : ℂ) * Complex.I)
        * Complex.exp (((2 * Real.pi * (l : ℝ) * w : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hpow : Complex.exp (((2 * Real.pi * (l : ℝ) * w : ℝ) : ℂ) * Complex.I)
      = (Complex.exp (((2 * Real.pi * w : ℝ) : ℂ) * Complex.I)) ^ l := by
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hcoef : ((coef K l).1.re * (-1 : ℝ) ^ (K + l) : ℂ)
      = (coef K l).1 * (-1 : ℂ) ^ (K + l) := by
    rcases (coef_unit K l hK2).1 with h | h
    · simp [h]
    · rw [h]
      norm_num
  rw [hexp, hpow, hcoef, pow_add,
    show (-(Complex.exp (((2 * Real.pi * w : ℝ) : ℂ) * Complex.I))) ^ l
      = (-1 : ℂ) ^ l * (Complex.exp (((2 * Real.pi * w : ℝ) : ℂ) * Complex.I)) ^ l by
      rw [neg_pow]]
  ring

/-- `‖Sexp K w‖ ≤ 5√K`. -/
theorem norm_Sexp_le {K : ℕ} (w : ℝ) : ‖Sexp K w‖ ≤ 5 * Real.sqrt (K : ℝ) := by
  rw [Sexp_eq]
  have h1 : ‖(-1 : ℂ) ^ K‖ = 1 := by
    rw [norm_pow, norm_neg, norm_one, one_pow]
  have h2 : ‖Complex.exp (((2 * Real.pi * (K : ℝ) * w : ℝ) : ℂ) * Complex.I)‖ = 1 :=
    Complex.norm_exp_ofReal_mul_I _
  have h3 : ‖rsPrefix (-(Complex.exp (((2 * Real.pi * w : ℝ) : ℂ) * Complex.I))) K‖
      ≤ 5 * Real.sqrt (K : ℝ) :=
    rsPrefix_bound (by rw [norm_neg, Complex.norm_exp_ofReal_mul_I]) K
  rw [norm_mul, norm_mul, h1, h2, one_mul, one_mul]
  exact h3

/-- **`sup_x |S_t(x)| ≤ 5√K`** — the bound used in `lem:bounded`. -/
theorem abs_Sfun_le {K : ℕ} (hK : 1 ≤ K) (t x : ℝ) :
    |Sfun K t x| ≤ 5 * Real.sqrt (K : ℝ) := by
  have h1 : |(Sexp K (t / K + x)).im| ≤ 5 * Real.sqrt (K : ℝ) :=
    (Complex.abs_im_le_norm _).trans (norm_Sexp_le _)
  have h2 : |(Sexp K (t / K - x)).im| ≤ 5 * Real.sqrt (K : ℝ) :=
    (Complex.abs_im_le_norm _).trans (norm_Sexp_le _)
  rw [Sfun_eq_im hK t x]
  have hsq : 0 ≤ Real.sqrt (K : ℝ) := Real.sqrt_nonneg _
  calc |1 / 2 * ((Sexp K (t / K + x)).im + (Sexp K (t / K - x)).im)|
      = 1 / 2 * |(Sexp K (t / K + x)).im + (Sexp K (t / K - x)).im| := by
        rw [abs_mul]
        norm_num
    _ ≤ 1 / 2 * (|(Sexp K (t / K + x)).im| + |(Sexp K (t / K - x)).im|) := by
        have := abs_add_le (Sexp K (t / K + x)).im (Sexp K (t / K - x)).im
        linarith
    _ ≤ 1 / 2 * (5 * Real.sqrt (K : ℝ) + 5 * Real.sqrt (K : ℝ)) := by linarith
    _ = 5 * Real.sqrt (K : ℝ) := by ring



/-- **`lem:bounded`, sup-norm part**: if `V_K(t) ≥ K/8` (the window lower bound),
then `|Y_t| = |S_t|/√(V_K(t)) ≤ 5√8`. -/
theorem abs_Y_le {K : ℕ} (hK : 1 ≤ K) (t x : ℝ) (hV : (K : ℝ) / 8 ≤ VK K t) :
    |Sfun K t x| / Real.sqrt (VK K t) ≤ 5 * Real.sqrt 8 := by
  have hKpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast (by omega : 0 < K)
  have hK8 : (0 : ℝ) < (K : ℝ) / 8 := by positivity
  have hVpos : 0 < VK K t := lt_of_lt_of_le hK8 hV
  have h1 : |Sfun K t x| ≤ 5 * Real.sqrt (K : ℝ) := abs_Sfun_le hK t x
  have hs8 : Real.sqrt ((K : ℝ) / 8) ≤ Real.sqrt (VK K t) := Real.sqrt_le_sqrt hV
  have hstep1 : |Sfun K t x| / Real.sqrt (VK K t)
      ≤ (5 * Real.sqrt (K : ℝ)) / Real.sqrt (VK K t) :=
    div_le_div_of_nonneg_right h1 (Real.sqrt_nonneg _)
  have hstep2 : (5 * Real.sqrt (K : ℝ)) / Real.sqrt (VK K t)
      ≤ (5 * Real.sqrt (K : ℝ)) / Real.sqrt ((K : ℝ) / 8) :=
    div_le_div_of_nonneg_left (by positivity) (Real.sqrt_pos.2 hK8) hs8
  have hsq : Real.sqrt ((K : ℝ) / 8) = Real.sqrt (K : ℝ) / Real.sqrt 8 :=
    Real.sqrt_div hKpos.le 8
  have hval : (5 * Real.sqrt (K : ℝ)) / Real.sqrt ((K : ℝ) / 8) = 5 * Real.sqrt 8 := by
    have hsK : Real.sqrt (K : ℝ) ≠ 0 := (Real.sqrt_pos.2 hKpos).ne'
    rw [hsq]
    field_simp
  linarith [hstep1, hstep2, hval]

end RudinDensity
end CenteredCube

#print axioms CenteredCube.RudinDensity.two_mul_sin_mul_cos
#print axioms CenteredCube.RudinDensity.rsPrefix_eq_sum
#print axioms CenteredCube.RudinDensity.Sfun_eq_im
#print axioms CenteredCube.RudinDensity.Sexp_eq
#print axioms CenteredCube.RudinDensity.norm_Sexp_le
#print axioms CenteredCube.RudinDensity.abs_Sfun_le
#print axioms CenteredCube.RudinDensity.abs_Y_le
