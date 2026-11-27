import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push

open Set Finset
namespace CubeSqrtOverlap

/-- On an ordered retained grid, k omitted packet starts contribute k full
spacings to the least possible cross-packet node distance. -/
theorem retained_node_distance {P T G a b : ℝ} (hP : T+G ≤ P)
    (hk : 0 ≤ P) (ha : 0 ≤ a) (haT : a ≤ T) (hb : 0 ≤ b) (i k : ℕ) :
    G+(k:ℝ)*P ≤ ((i+k+1:ℕ):ℝ)*P+b-((i:ℝ)*P+a) := by
  push_cast
  linarith only [hP,haT,hb]

theorem sum_range_geometric_le (x : ℝ) (hx : 0 ≤ x) (h1 : x < 1) (n : ℕ) :
    (∑ k ∈ range n, x^k) ≤ 1/(1-x) := by
  induction n with
  | zero => simpa only [sum_range_zero] using (div_nonneg (by norm_num : (0:ℝ) ≤ 1) (sub_nonneg.mpr h1.le))
  | succ n ih =>
    rw [sum_range_succ']
    simp only [pow_succ, pow_zero]
    rw [← sum_mul]
    have h := mul_le_mul_of_nonneg_right ih hx
    have hId : (1/(1-x))*x+1 = 1/(1-x) := by field_simp [ne_of_gt (sub_pos.mpr h1)] <;> ring
    exact (add_le_add_left h _).trans_eq hId

/-- Sum the exponential near-region envelope over all retained packet centers
and both finite node sets. P is the stride, G is the empty gap. Use C=0 on
non-near pairs, which avoids counting the same contributions twice. -/
theorem retained_near_total
    {I J : Type*} [Fintype I] [Fintype J]
    (B : ℕ) (R : Finset ℕ) (P T G c C : ℝ) (hP : 0 < P) (hc : 0 < c) (hC : 0 ≤ C)
    (hspacing : T+G ≤ P)
    (offsetL : I → ℝ) (offsetR : J → ℝ)
    (hL0 : ∀ i, 0 ≤ offsetL i) (hLT : ∀ i, offsetL i ≤ T)
    (hR0 : ∀ j, 0 ≤ offsetR j)
    (W : ℕ → ℕ → I → J → ℝ)
    (hW : ∀ i ∈ R, ∀ k ∈ range (B-i-1), ∀ l j, W i k l j ≤
      C*Real.exp (-c*(((i+k+1:ℕ):ℝ)*P+offsetR j-((i:ℝ)*P+offsetL l)))) :
    (∑ i ∈ R, ∑ k ∈ range (B-i-1), ∑ l : I, ∑ j : J, W i k l j) ≤
      (R.card:ℝ)*(Fintype.card I:ℝ)*(Fintype.card J:ℝ)*C*Real.exp (-c*G) /
        (1-Real.exp (-c*P)) := by
  let x := Real.exp (-c*P)
  let A := (Fintype.card I:ℝ)*(Fintype.card J:ℝ)*C*Real.exp (-c*G)
  have hx : 0 ≤ x := (Real.exp_pos _).le
  have h1 : x < 1 := by
    dsimp [x]
    rw [Real.exp_lt_one_iff]
    nlinarith only [mul_pos hc hP]
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hCell (i : ℕ) (hi : i ∈ R) (k : ℕ) (hk : k ∈ range (B-i-1)) (l : I) (j : J) :
      W i k l j ≤ C*Real.exp (-c*G)*x^k := by
    have h := retained_node_distance hspacing hP.le (hL0 l) (hLT l) (hR0 j) i k
    calc
      _ ≤ C*Real.exp (-c*(G+(k:ℝ)*P)) := (hW i hi k hk l j).trans
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left h (by linarith))) hC)
      _ = _ := by
        dsimp [x]
        rw [← Real.exp_nat_mul,mul_assoc,← Real.exp_add]
        congr 1
        ring
  have hInner (i : ℕ) (hi : i ∈ R) (k : ℕ) (hk : k ∈ range (B-i-1)) : (∑ l : I, ∑ j : J, W i k l j) ≤ A*x^k := by
    calc
      _ ≤ ∑ _l : I, ∑ _j : J, C*Real.exp (-c*G)*x^k :=
        sum_le_sum fun l _ ↦ sum_le_sum fun j _ ↦ hCell i hi k hk l j
      _ = _ := by simp [A]; ring
  have hRow (i : ℕ) (hi : i ∈ R) : (∑ k ∈ range (B-i-1), ∑ l : I, ∑ j : J, W i k l j) ≤ A*(1/(1-x)) := by
    calc
      _ ≤ ∑ k ∈ range (B-i-1), A*x^k := sum_le_sum fun k hk ↦ hInner i hi k hk
      _ ≤ _ := by
        rw [← mul_sum]
        exact mul_le_mul_of_nonneg_left (sum_range_geometric_le x hx h1 _) hA
  calc
    _ ≤ ∑ _i ∈ R, A*(1/(1-x)) := sum_le_sum fun i hi ↦ hRow i hi
    _ = _ := by simp [A,x,div_eq_mul_inv,mul_assoc]

end CubeSqrtOverlap
#print axioms CubeSqrtOverlap.retained_near_total
