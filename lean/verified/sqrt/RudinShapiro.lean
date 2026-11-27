import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
The polynomial recursion in the Rudin–Shapiro manuscript, Section 2.
A pair stores the P and Q polynomials evaluated at a fixed z.
-/
namespace CenteredCube.RudinShapiro

def polys (z : ℂ) : ℕ → ℂ × ℂ
  | 0 => (1, 1)
  | q + 1 =>
    let (p, s) := polys z q
    (p + z ^ (2 ^ q) * s, p - z ^ (2 ^ q) * s)

/-- Truncate both recursive polynomials after their first n monomials.
The second block begins at index 2^q and carries the Q polynomial. -/
def prefixes (z : ℂ) : ℕ → ℕ → ℂ × ℂ
  | 0, n => if n = 0 then (0, 0) else (1, 1)
  | q + 1, n =>
    if n ≤ 2 ^ q then ((prefixes z q n).1, (prefixes z q n).1)
    else
      let p := (polys z q).1
      let s := (prefixes z q (n - 2 ^ q)).2
      (p + z ^ (2 ^ q) * s, p - z ^ (2 ^ q) * s)

theorem prefixes_full (z : ℂ) (q : ℕ) : prefixes z q (2 ^ q) = polys z q := by
  induction q with
  | zero => norm_num [prefixes, polys]
  | succ q ih =>
    have hpos : 0 < (2 : ℕ) ^ q := pow_pos (by decide) _
    have hgt : ¬ (2 : ℕ) ^ (q + 1) ≤ 2 ^ q := by
      rw [pow_succ]
      omega
    have hsub : (2 : ℕ) ^ (q + 1) - 2 ^ q = 2 ^ q := by
      rw [pow_succ]
      omega
    simp [prefixes, polys, hgt, hsub, ih]

private theorem norm_parallelogram (p s : ℂ) :
    ‖p + s‖ ^ 2 + ‖p - s‖ ^ 2 = 2 * (‖p‖ ^ 2 + ‖s‖ ^ 2) := by
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
    Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im]
  ring

/-- The exact unit-circle energy of the full P/Q pair. -/
theorem energy {z : ℂ} (hz : ‖z‖ = 1) (q : ℕ) :
    ‖(polys z q).1‖ ^ 2 + ‖(polys z q).2‖ ^ 2 = (2 : ℝ) ^ (q + 1) := by
  induction q with
  | zero => norm_num [polys]
  | succ q ih =>
    change ‖((polys z q).1 + z ^ (2 ^ q) * (polys z q).2)‖ ^ 2 +
      ‖((polys z q).1 - z ^ (2 ^ q) * (polys z q).2)‖ ^ 2 =
      (2 : ℝ) ^ (q + 1 + 1)
    rw [norm_parallelogram, norm_mul, norm_pow, hz, one_pow, one_mul, ih, pow_succ]
    ring

private theorem full_norm_bound {z : ℂ} (hz : ‖z‖ = 1) (q : ℕ) :
    ‖(polys z q).1‖ ≤ (3 / 2) * Real.sqrt (((2 : ℕ) ^ q : ℕ) : ℝ) := by
  have h := energy hz q
  rw [show (2 : ℝ) ^ (q + 1) = 2 ^ q * 2 from pow_succ _ _] at h
  push_cast
  have hs := Real.sq_sqrt (show 0 ≤ (2 : ℝ) ^ q by positivity)
  have hn : 0 ≤ ‖(polys z q).2‖ ^ 2 := sq_nonneg _
  have hm : 0 ≤ Real.sqrt ((2 : ℝ) ^ q) := Real.sqrt_nonneg _
  by_contra! hlt
  have hmul := mul_lt_mul_of_pos_right hlt
    (show 0 < ‖(polys z q).1‖ + (3 / 2) * Real.sqrt ((2 : ℝ) ^ q) by
      nlinarith [norm_nonneg (polys z q).1])
  nlinarith

/-- The triangle-inequality budget in the recursive prefix estimate. -/
private theorem sqrt_budget {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (hba : b ≤ a) :
    (3 / 2) * Real.sqrt a + 5 * Real.sqrt b ≤ 5 * Real.sqrt (a + b) := by
  have ha0 := ha.le
  have hab : 0 ≤ a + b := by linarith
  have hs₁ := Real.sq_sqrt ha0
  have hs₂ := Real.sq_sqrt hb
  have hs₃ := Real.sq_sqrt hab
  have hp : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have hq : 0 ≤ Real.sqrt b := Real.sqrt_nonneg _
  have hr : 0 ≤ Real.sqrt (a + b) := Real.sqrt_nonneg _
  have hq₁ : Real.sqrt b ≤ Real.sqrt a := Real.sqrt_le_sqrt hba
  have hr₁ : Real.sqrt (a + b) ≤ 2 * Real.sqrt a := by
    by_contra! hn
    have hh := mul_lt_mul_of_pos_right hn
      (show 0 < Real.sqrt (a + b) + 2 * Real.sqrt a by linarith)
    nlinarith
  have hdiff : 0 ≤ Real.sqrt (a + b) - Real.sqrt b :=
    sub_nonneg.mpr (Real.sqrt_le_sqrt (by linarith))
  have hprod := mul_le_mul_of_nonneg_left
    (show Real.sqrt (a + b) + Real.sqrt b ≤ 3 * Real.sqrt a by linarith) hdiff
  have hd : Real.sqrt a ≤ 3 * (Real.sqrt (a + b) - Real.sqrt b) := by
    by_contra! hn
    have hh := mul_lt_mul_of_pos_right hn hp
    nlinarith
  linarith

/-- Simultaneous P- and Q-prefix bounds for lengths within the polynomial. -/
theorem prefix_bound {z : ℂ} (hz : ‖z‖ = 1) (q n : ℕ) (hn : n ≤ 2 ^ q) :
    ‖(prefixes z q n).1‖ ≤ 5 * Real.sqrt n ∧
      ‖(prefixes z q n).2‖ ≤ 5 * Real.sqrt n := by
  induction q generalizing n with
  | zero =>
    have h : n ≤ 1 := by simpa using hn
    have hn₀ : n = 0 ∨ n = 1 := by omega
    rcases hn₀ with rfl | rfl <;> norm_num [prefixes]
  | succ q ih =>
    by_cases h : n ≤ 2 ^ q
    · simpa [prefixes, h] using And.intro (ih n h).1 (ih n h).1
    · let m := (2 : ℕ) ^ q
      have hm : 0 < m := pow_pos (by decide) _
      have hnm : m ≤ n := by dsimp [m]; omega
      have hd : n - m ≤ m := by
        rw [pow_succ] at hn
        dsimp [m]
        omega
      have hshift : ‖z ^ m * (prefixes z q (n - m)).2‖ ≤ 5 * Real.sqrt ↑(n - m) := by
        rw [norm_mul, norm_pow, hz, one_pow, one_mul]
        exact (ih (n - m) hd).2
      have hsum : (m : ℝ) + ↑(n - m) = ↑n := by
        rw [Nat.cast_sub hnm]
        ring
      have hbudget := sqrt_budget (a := (m : ℝ)) (b := ((n - m : ℕ) : ℝ))
        (by exact_mod_cast hm) (by positivity) (by exact_mod_cast hd)
      rw [hsum] at hbudget
      have hP := full_norm_bound hz q
      change ‖(polys z q).1‖ ≤ (3 / 2) * Real.sqrt (m : ℝ) at hP
      rw [prefixes, ite_eq_right h]
      constructor
      · exact (norm_add_le _ _).trans ((add_le_add hP hshift).trans hbudget)
      · exact (norm_sub_le _ _).trans ((add_le_add hP hshift).trans hbudget)

/-- Once the level contains n monomials, its P-prefix is unchanged at the next level. -/
theorem prefix_stable (z : ℂ) (q n : ℕ) (hn : n ≤ 2 ^ q) :
    (prefixes z (q + 1) n).1 = (prefixes z q n).1 := by
  simp [prefixes, hn]

end CenteredCube.RudinShapiro

#print axioms CenteredCube.RudinShapiro.prefixes_full
#print axioms CenteredCube.RudinShapiro.energy
#print axioms CenteredCube.RudinShapiro.prefix_bound
#print axioms CenteredCube.RudinShapiro.prefix_stable
