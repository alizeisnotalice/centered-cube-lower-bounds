/-
Coefficient extraction for the Rudin–Shapiro recursion.

`RudinShapiro.polys z q = (P_q(z), Q_q(z))` is defined by

  `P_0 = Q_0 = 1`,  `P_{q+1} = P_q + z^{2^q} Q_q`,  `Q_{q+1} = P_q - z^{2^q} Q_q`.

This file records the coefficients of both polynomials as an explicit family
`coef q j : ℂ × ℂ` (the `P`- and `Q`-coefficient of `z^j`), and proves that the
recursion is exactly the coefficient recursion

  `coef (q+1) j = coef q j`                     if `j < 2^q`,
  `coef (q+1) j = ((coef q (j-2^q)).2, -(coef q (j-2^q)).2)`  otherwise,

so that `P_q(z) = ∑_{j<2^q} (coef q j).1 z^j` and likewise for `Q_q`.

Consequences used downstream: every `Rudin–Shapiro` prefix `rsPrefix z N` is a
polynomial in `z` of degree `< N` (`prefixes_poly`, `rsPrefix_poly`), which is what
turns the weighted sum into the manuscript's cosine series.
-/
import RudinShapiro
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Analysis.Complex.Basic

open Finset
open scoped BigOperators

namespace CenteredCube
namespace RudinDensity

/-- The `P`- and `Q`-coefficient of `z^j` at recursion level `q`.

Since `Q_{q+1} = P_q - z^{2^q} Q_q`, the lower half of the `Q`-coefficients is the
lower half of the `P`-coefficients, not the lower half of the `Q`-coefficients. -/
noncomputable def coef : ℕ → ℕ → ℂ × ℂ
  | 0 => fun j => if j = 0 then (1, 1) else (0, 0)
  | q + 1 => fun j =>
      if j < 2 ^ q then
        let c := (coef q j).1
        (c, c)
      else
        let s := (coef q (j - 2 ^ q)).2
        (s, -s)

theorem coef_succ_of_lt {q j : ℕ} (hj : j < 2 ^ q) :
    coef (q + 1) j = ((coef q j).1, (coef q j).1) := by
  simp only [coef]
  rw [if_pos hj]

theorem coef_succ_of_ge {q j : ℕ} (hj : ¬ j < 2 ^ q) :
    coef (q + 1) j =
      (let s := (coef q (j - 2 ^ q)).2; (s, -s)) := by
  simp only [coef]
  rw [if_neg hj]

/-- The coefficient recursion computes the two recursive polynomials:
`P_q(z) = ∑_{j<2^q} (coef q j).1 z^j`, `Q_q(z) = ∑_{j<2^q} (coef q j).2 z^j`. -/
theorem polys_coef (q : ℕ) (z : ℂ) :
    (RudinShapiro.polys z q).1 = ∑ j ∈ range (2 ^ q), (coef q j).1 * z ^ j ∧
    (RudinShapiro.polys z q).2 = ∑ j ∈ range (2 ^ q), (coef q j).2 * z ^ j := by
  induction q with
  | zero =>
    constructor <;> simp [RudinShapiro.polys, coef]
  | succ q ih =>
    obtain ⟨hP, hQ⟩ := ih
    have hstepP : (RudinShapiro.polys z (q + 1)).1
        = (RudinShapiro.polys z q).1 + z ^ (2 ^ q) * (RudinShapiro.polys z q).2 := rfl
    have hstepQ : (RudinShapiro.polys z (q + 1)).2
        = (RudinShapiro.polys z q).1 - z ^ (2 ^ q) * (RudinShapiro.polys z q).2 := rfl
    have hpow : 2 ^ (q + 1) = 2 ^ q + 2 ^ q := by rw [pow_succ]; ring
    constructor
    · rw [hstepP, hP, hQ, Finset.mul_sum, hpow, Finset.sum_range_add]
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro j hj
      have hj' : j < 2 ^ q := Finset.mem_range.mp hj
      have h1 : (coef (q + 1) j).1 = (coef q j).1 := by rw [coef_succ_of_lt hj']
      have h2 : (coef (q + 1) (2 ^ q + j)).1 = (coef q j).2 := by
        rw [coef_succ_of_ge (by omega)]
        simp
      rw [h1, h2, pow_add]
      ring
    · rw [hstepQ, hP, hQ, Finset.mul_sum, hpow, Finset.sum_range_add]
      rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro j hj
      have hj' : j < 2 ^ q := Finset.mem_range.mp hj
      have h1 : (coef (q + 1) j).2 = (coef q j).1 := by rw [coef_succ_of_lt hj']
      have h2 : (coef (q + 1) (2 ^ q + j)).2 = -((coef q j).2) := by
        rw [coef_succ_of_ge (by omega)]
        simp
      rw [h1, h2, pow_add]
      ring


/-- Every prefix stored by the recursion is a polynomial of degree `< n`:
`(prefixes z q n).1` and `.2` are both finite sums `∑_{j<n} c_j z^j`. -/
theorem prefixes_poly : ∀ (q n : ℕ), n ≤ 2 ^ q → ∀ z : ℂ, ∃ cP cQ : ℕ → ℂ,
    (RudinShapiro.prefixes z q n).1 = ∑ j ∈ range n, cP j * z ^ j ∧
    (RudinShapiro.prefixes z q n).2 = ∑ j ∈ range n, cQ j * z ^ j := by
  intro q
  induction q with
  | zero =>
    intro n hn z
    have hn' : n = 0 ∨ n = 1 := by omega
    rcases hn' with rfl | rfl
    · exact ⟨fun _ => 0, fun _ => 0, by simp [RudinShapiro.prefixes],
        by simp [RudinShapiro.prefixes]⟩
    · exact ⟨fun _ => 1, fun _ => 1, by simp [RudinShapiro.prefixes],
        by simp [RudinShapiro.prefixes]⟩
  | succ q ih =>
    intro n hn z
    by_cases h : n ≤ 2 ^ q
    · obtain ⟨cP, cQ, h1, h2⟩ := ih n h z
      refine ⟨cP, cP, ?_, ?_⟩
      · simpa [RudinShapiro.prefixes, h] using h1
      · simpa [RudinShapiro.prefixes, h] using h1
    · have hm : 0 < 2 ^ q := pow_pos (by norm_num) q
      have hmn : 2 ^ q < n := lt_of_not_ge h
      have hnm : n - 2 ^ q ≤ 2 ^ q := by
        rw [pow_succ] at hn
        omega
      obtain ⟨-, cQ, -, hS⟩ := ih (n - 2 ^ q) hnm z
      obtain ⟨hP, -⟩ := polys_coef q z
      have hdefP : (RudinShapiro.prefixes z (q + 1) n).1
          = (RudinShapiro.polys z q).1
            + z ^ (2 ^ q) * (RudinShapiro.prefixes z q (n - 2 ^ q)).2 := by
        simp [RudinShapiro.prefixes, h]
      have hdefQ : (RudinShapiro.prefixes z (q + 1) n).2
          = (RudinShapiro.polys z q).1
            - z ^ (2 ^ q) * (RudinShapiro.prefixes z q (n - 2 ^ q)).2 := by
        simp [RudinShapiro.prefixes, h]
      have hsplit : n = 2 ^ q + (n - 2 ^ q) := (Nat.add_sub_cancel' (le_of_lt hmn)).symm
      refine ⟨fun j => if j < 2 ^ q then (coef q j).1 else cQ (j - 2 ^ q),
        fun j => if j < 2 ^ q then (coef q j).1 else -(cQ (j - 2 ^ q)), ?_, ?_⟩
      · have h1 : (∑ j ∈ range (2 ^ q), (coef q j).1 * z ^ j)
            = ∑ j ∈ range (2 ^ q),
                (if j < 2 ^ q then (coef q j).1 else cQ (j - 2 ^ q)) * z ^ j := by
          refine Finset.sum_congr rfl (fun j hj => ?_)
          rw [if_pos (Finset.mem_range.mp hj)]
        have h2 : (∑ i ∈ range (n - 2 ^ q), z ^ (2 ^ q) * (cQ i * z ^ i))
            = ∑ x ∈ range (n - 2 ^ q),
                (if (2 ^ q + x) < 2 ^ q then (coef q (2 ^ q + x)).1
                  else cQ ((2 ^ q + x) - 2 ^ q)) * z ^ (2 ^ q + x) := by
          refine Finset.sum_congr rfl (fun x _ => ?_)
          rw [if_neg (by omega : ¬ (2 ^ q + x) < 2 ^ q), Nat.add_sub_cancel_left, pow_add]
          ring_nf
        rw [hdefP, hP, hS, Finset.mul_sum]
        conv_rhs => rw [hsplit]
        rw [Finset.sum_range_add, h1, h2]
      · have h1 : (∑ j ∈ range (2 ^ q), (coef q j).1 * z ^ j)
            = ∑ j ∈ range (2 ^ q),
                (if j < 2 ^ q then (coef q j).1 else -(cQ (j - 2 ^ q))) * z ^ j := by
          refine Finset.sum_congr rfl (fun j hj => ?_)
          rw [if_pos (Finset.mem_range.mp hj)]
        have h2pos : (∑ i ∈ range (n - 2 ^ q), cQ i * z ^ (2 ^ q + i))
            = ∑ i ∈ range (n - 2 ^ q), cQ i * z ^ (2 ^ q + i) := rfl
        have h3 : (∑ x ∈ range (n - 2 ^ q),
              (if (2 ^ q + x) < 2 ^ q then (coef q (2 ^ q + x)).1
                else -(cQ ((2 ^ q + x) - 2 ^ q))) * z ^ (2 ^ q + x))
            = - ∑ i ∈ range (n - 2 ^ q), cQ i * z ^ (2 ^ q + i) := by
          rw [← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl (fun x _ => ?_)
          rw [if_neg (by omega : ¬ (2 ^ q + x) < 2 ^ q), Nat.add_sub_cancel_left]
          ring
        have hmul : (∑ i ∈ range (n - 2 ^ q), z ^ (2 ^ q) * (cQ i * z ^ i))
            = ∑ i ∈ range (n - 2 ^ q), cQ i * z ^ (2 ^ q + i) := by
          refine Finset.sum_congr rfl (fun x _ => ?_)
          rw [pow_add]
          ring
        rw [hdefQ, hP, hS, Finset.mul_sum]
        conv_rhs => rw [hsplit]
        rw [Finset.sum_range_add, h1, h3, hmul]
        ring

/-- The prefix used at level `N`, `(prefixes z N N).1`, is a polynomial of degree `< N`.
This is the form taken by `rsPrefix` in `Abel.lean`. -/
theorem self_prefix_poly (N : ℕ) (z : ℂ) : ∃ c : ℕ → ℂ,
    (RudinShapiro.prefixes z N N).1 = ∑ j ∈ range N, c j * z ^ j := by
  have hN : N ≤ 2 ^ N := by
    induction N with
    | zero => simp
    | succ k ih =>
      have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
      rw [pow_succ, mul_two]
      omega
  obtain ⟨cP, -, h1, -⟩ := prefixes_poly N N hN z
  exact ⟨cP, h1⟩


/-- Every coefficient of `P_q` and `Q_q` is `+1` or `-1`: the recursion only ever
adds, subtracts or shifts coefficients, starting from `1`. -/
theorem coef_unit : ∀ (q j : ℕ), j < 2 ^ q →
    ((coef q j).1 = 1 ∨ (coef q j).1 = -1) ∧
      ((coef q j).2 = 1 ∨ (coef q j).2 = -1)
  | 0, j, hj => by
    have hj0 : j = 0 := by omega
    subst hj0
    simp [coef]
  | q + 1, j, hj => by
    by_cases h : j < 2 ^ q
    · rw [coef_succ_of_lt h]
      have hu := (coef_unit q j h).1
      simpa only [Prod.fst, Prod.snd] using And.intro hu hu
    · rw [coef_succ_of_ge h]
      have hjm : j - 2 ^ q < 2 ^ q := by
        rw [pow_succ] at hj
        omega
      have hunit := (coef_unit q (j - 2 ^ q) hjm).2
      constructor
      · simpa using hunit
      · rcases hunit with h1 | h1 <;> simp [h1]

end RudinDensity
end CenteredCube

#print axioms CenteredCube.RudinDensity.polys_coef
#print axioms CenteredCube.RudinDensity.prefixes_poly
#print axioms CenteredCube.RudinDensity.self_prefix_poly
#print axioms CenteredCube.RudinDensity.coef_unit
