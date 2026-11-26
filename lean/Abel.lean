/-
The Rudin–Shapiro density of the `√n/log n` manuscript: Abel summation.

The manuscript (eq. (1.2) and Lemma 2.3) builds, for `K ≥ 1`,

  `ρ_K(x) = 1 + (1/(30√K)) ∑_{l<K} ε_l (1 + l/K) cos(2π(K+l)x)`,

and proves `sup_{|z|=1} |∑_{l<K} ε_l (1+l/K) z^l| ≤ 15√K`, whence
`1/2 ≤ ρ_K ≤ 3/2`, `∫₀¹ ρ_K = 1`.

Here the Rudin–Shapiro partial sums are the ones already verified in
`RudinShapiro.lean`: `rsPrefix z N` is the `P`-prefix of length `N`, i.e. the
manuscript's `F_N(z) = ∑_{l<N} ε_l z^l`, and the coefficients are recovered as
the differences `F_{l+1} - F_l = ε_l z^l`.  Consequently the weighted sum below
*is* the manuscript's `∑_{l<K} ε_l (1+l/K) z^l`, and

* `weighted_bound` proves the manuscript's `15√K` estimate by Abel summation,
  with the verified `5√N` prefix bound as the only input;
* `rho_bounds` proves `1/2 ≤ ρ_K ≤ 3/2`.

Remaining gap for the full normalisation statement of the manuscript: that the
coefficients `F_{l+1} - F_l` are of the form `ε_l z^l` with `ε_l ∈ {±1}`, and
that `ρ_K` therefore equals the displayed real cosine series (which would give
`∫₀¹ ρ_K = 1` by termwise integration).  Both are elementary facts about the
recursion; neither is assumed anywhere below.
-/
import RudinShapiro
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Trigonometric

open Finset
open scoped BigOperators

namespace CenteredCube
namespace RudinDensity

/-- The `P`-prefix of length `N`, i.e. the manuscript's `F_N(z) = ∑_{l<N} ε_l z^l`.
It does not depend on the recursion level, by `RudinShapiro.prefix_stable`. -/
noncomputable def rsPrefix (z : ℂ) (N : ℕ) : ℂ :=
  (RudinShapiro.prefixes z N N).1

/-- `N ≤ 2^N`, so the verified prefix bound applies at level `N`. -/
theorem le_two_pow : ∀ n : ℕ, n ≤ 2 ^ n
  | 0 => by simp
  | n + 1 => by
    have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    have ih : n ≤ 2 ^ n := le_two_pow n
    rw [pow_succ, mul_two]
    omega

/-- Rudin's partial-sum bound, inherited from the verified `RudinShapiro.prefix_bound`. -/
theorem rsPrefix_bound {z : ℂ} (hz : ‖z‖ = 1) (N : ℕ) :
    ‖rsPrefix z N‖ ≤ 5 * Real.sqrt (N : ℝ) :=
  (RudinShapiro.prefix_bound hz N N (le_two_pow N)).1

theorem rsPrefix_zero (z : ℂ) : rsPrefix z 0 = 0 := by
  simp [rsPrefix, RudinShapiro.prefixes]

/-- The weighted sum `∑_{l<K} ε_l (1 + l/K) z^l`, written with
`ε_l z^l = F_{l+1} - F_l`. -/
noncomputable def weightedSum (z : ℂ) (K : ℕ) : ℂ :=
  ∑ l ∈ range K, ((1 : ℂ) + (l : ℂ) / (K : ℂ)) * (rsPrefix z (l + 1) - rsPrefix z l)

/-- Telescoping of the prefix differences: `∑_{j<n} (F_{j+1} - F_j) = F_n`. -/
theorem sum_prefix_diff (z : ℂ) (n : ℕ) :
    ∑ j ∈ range n, (rsPrefix z (j + 1) - rsPrefix z j) = rsPrefix z n := by
  rw [Finset.sum_range_sub (fun i => rsPrefix z i) n, rsPrefix_zero, sub_zero]

/-- Abel summation, in the form needed here. -/
theorem weightedSum_abel {z : ℂ} {K : ℕ} (hK : 1 ≤ K) :
    weightedSum z K =
      ((1 : ℂ) + (((K - 1 : ℕ) : ℂ) / (K : ℂ))) * rsPrefix z K -
        (1 / (K : ℂ)) * ∑ i ∈ range (K - 1), rsPrefix z (i + 1) := by
  have hdiff : ∀ i : ℕ,
      ((1 : ℂ) + (((i + 1 : ℕ) : ℂ)) / (K : ℂ)) - ((1 : ℂ) + (i : ℂ) / (K : ℂ))
        = 1 / (K : ℂ) := by
    intro i
    have hcast : ((i + 1 : ℕ) : ℂ) = (i : ℂ) + 1 := by push_cast; ring
    rw [hcast]
    ring
  have h := Finset.sum_range_by_parts
    (f := fun l : ℕ => (1 : ℂ) + (l : ℂ) / (K : ℂ))
    (g := fun l : ℕ => rsPrefix z (l + 1) - rsPrefix z l) (n := K)
  simp only [smul_eq_mul] at h
  unfold weightedSum
  rw [h]
  simp only [sum_prefix_diff, hdiff]
  rw [Finset.mul_sum]

/-- **The manuscript's `15√K` estimate.**  For `|z| = 1` and `K ≥ 1`,
`|∑_{l<K} ε_l (1 + l/K) z^l| ≤ 15√K`. -/
theorem weighted_bound {z : ℂ} (hz : ‖z‖ = 1) {K : ℕ} (hK : 1 ≤ K) :
    ‖weightedSum z K‖ ≤ 15 * Real.sqrt (K : ℝ) := by
  have hKpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast (by omega : 0 < K)
  have hsqrt : 0 < Real.sqrt (K : ℝ) := Real.sqrt_pos.2 hKpos
  rw [weightedSum_abel hK]
  have htail : ‖∑ i ∈ range (K - 1), rsPrefix z (i + 1)‖ ≤ 5 * (K : ℝ) * Real.sqrt (K : ℝ) := by
    refine (norm_sum_le _ _).trans ?_
    have hterm : ∀ i ∈ range (K - 1), ‖rsPrefix z (i + 1)‖ ≤ 5 * Real.sqrt (K : ℝ) := by
      intro i hi
      refine (rsPrefix_bound hz (i + 1)).trans ?_
      have hi' : i + 1 ≤ K := by
        have := Finset.mem_range.mp hi
        omega
      have hle : Real.sqrt ((i + 1 : ℕ) : ℝ) ≤ Real.sqrt (K : ℝ) :=
        Real.sqrt_le_sqrt (by exact_mod_cast hi')
      linarith
    refine (Finset.sum_le_sum hterm).trans ?_
    have hcard : ((K - 1 : ℕ) : ℝ) ≤ (K : ℝ) := by
      exact_mod_cast Nat.sub_le K 1
    calc ∑ _i ∈ range (K - 1), 5 * Real.sqrt (K : ℝ)
        = ((K - 1 : ℕ) : ℝ) * (5 * Real.sqrt (K : ℝ)) := by simp
      _ ≤ (K : ℝ) * (5 * Real.sqrt (K : ℝ)) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = 5 * (K : ℝ) * Real.sqrt (K : ℝ) := by ring
  have hweight : ‖(1 : ℂ) + (((K - 1 : ℕ) : ℂ)) / (K : ℂ)‖ ≤ 2 := by
    have hratio : ‖(((K - 1 : ℕ) : ℂ)) / (K : ℂ)‖ ≤ 1 := by
      rw [norm_div, Complex.norm_natCast, Complex.norm_natCast, div_le_one hKpos]
      exact_mod_cast Nat.sub_le K 1
    calc ‖(1 : ℂ) + (((K - 1 : ℕ) : ℂ)) / (K : ℂ)‖
        ≤ ‖(1 : ℂ)‖ + ‖(((K - 1 : ℕ) : ℂ)) / (K : ℂ)‖ := norm_add_le _ _
      _ ≤ 1 + 1 := by rw [norm_one]; linarith
      _ = 2 := by norm_num
  have h1 : ‖((1 : ℂ) + (((K - 1 : ℕ) : ℂ) / (K : ℂ))) * rsPrefix z K‖ ≤
      2 * (5 * Real.sqrt (K : ℝ)) := by
    rw [norm_mul]
    exact mul_le_mul hweight (rsPrefix_bound hz K) (norm_nonneg _) (by norm_num)
  have h2 : ‖(1 / (K : ℂ)) * ∑ i ∈ range (K - 1), rsPrefix z (i + 1)‖ ≤
      5 * Real.sqrt (K : ℝ) := by
    rw [norm_mul, norm_div, norm_one, Complex.norm_natCast]
    have hbound : 1 / (K : ℝ) * ‖∑ i ∈ range (K - 1), rsPrefix z (i + 1)‖
        ≤ 1 / (K : ℝ) * (5 * (K : ℝ) * Real.sqrt (K : ℝ)) :=
      mul_le_mul_of_nonneg_left htail (by positivity)
    refine hbound.trans ?_
    have hKne : (K : ℝ) ≠ 0 := hKpos.ne'
    have : 1 / (K : ℝ) * (5 * (K : ℝ) * Real.sqrt (K : ℝ)) = 5 * Real.sqrt (K : ℝ) := by
      field_simp
    rw [this]
  refine (norm_sub_le _ _).trans ?_
  linarith

/-- The point `z = e^{2πix}` on the unit circle. -/
noncomputable def zof (x : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * (x : ℂ))

theorem norm_zof (x : ℝ) : ‖zof x‖ = 1 := by
  have h : zof x = Complex.exp (((2 * Real.pi * x : ℝ)) * Complex.I) := by
    unfold zof
    push_cast
    ring_nf
  rw [h, Complex.norm_exp_ofReal_mul_I]

/-- The manuscript's density `ρ_K`. -/
noncomputable def rho (K : ℕ) (x : ℝ) : ℝ :=
  1 + (1 / (30 * Real.sqrt (K : ℝ))) *
    Complex.re ((zof x) ^ K * weightedSum (zof x) K)

/-- **`1/2 ≤ ρ_K ≤ 3/2`**, the pointwise bound of the manuscript's Lemma 2.3. -/
theorem rho_bounds {K : ℕ} (hK : 1 ≤ K) (x : ℝ) :
    1 / 2 ≤ rho K x ∧ rho K x ≤ 3 / 2 := by
  have hKpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast (by omega : 0 < K)
  have hsqrt : 0 < Real.sqrt (K : ℝ) := Real.sqrt_pos.2 hKpos
  have hz : ‖zof x‖ = 1 := norm_zof x
  have hWs : ‖weightedSum (zof x) K‖ ≤ 15 * Real.sqrt (K : ℝ) := weighted_bound hz hK
  have hzk : ‖(zof x) ^ K‖ = 1 := by rw [norm_pow, hz, one_pow]
  have hre : |Complex.re ((zof x) ^ K * weightedSum (zof x) K)| ≤ 15 * Real.sqrt (K : ℝ) := by
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul, hzk, one_mul]
    exact hWs
  have hcoef : 0 < 1 / (30 * Real.sqrt (K : ℝ)) := by positivity
  have hkey : (1 / (30 * Real.sqrt (K : ℝ))) *
      |Complex.re ((zof x) ^ K * weightedSum (zof x) K)| ≤ 1 / 2 := by
    have hmul := mul_le_mul_of_nonneg_left hre hcoef.le
    refine hmul.trans ?_
    rw [show (1 / (30 * Real.sqrt (K : ℝ))) * (15 * Real.sqrt (K : ℝ)) = 1 / 2 by
      rw [div_mul_eq_mul_div, div_eq_iff (by positivity)]
      ring]
  have habs : |(1 / (30 * Real.sqrt (K : ℝ))) *
      Complex.re ((zof x) ^ K * weightedSum (zof x) K)| ≤ 1 / 2 := by
    rw [abs_mul, abs_of_pos hcoef]
    exact hkey
  constructor
  · have hlow := neg_le_of_abs_le habs
    unfold rho
    linarith
  · have hup := le_of_abs_le habs
    unfold rho
    linarith

end RudinDensity
end CenteredCube

#print axioms CenteredCube.RudinDensity.rsPrefix_bound
#print axioms CenteredCube.RudinDensity.weightedSum_abel
#print axioms CenteredCube.RudinDensity.weighted_bound
#print axioms CenteredCube.RudinDensity.rho_bounds
