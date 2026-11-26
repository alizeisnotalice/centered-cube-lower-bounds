import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Finset

namespace CenteredCube

/-- A two-term estimate for log(1+s), with the paper's cubic error budget. -/
theorem log_one_add_lower {s : ℝ} (hs : |s| ≤ 1 / 2) :
    s - s^2 / 2 - 3 * |s|^3 ≤ Real.log (1 + s) := by
  have hlt : |-s| < 1 := by rw [abs_neg]; linarith
  have h := Real.abs_log_sub_add_sum_range_le hlt 2
  have heq : (∑ i ∈ range 2, (-s) ^ (i + 1) / ((i : ℝ) + 1)) =
      -s + s^2 / 2 := by
    norm_num [sum_range_succ] <;> ring
  rw [heq, abs_neg, sub_neg_eq_add] at h
  have hp : 0 < 1 - |s| := by linarith
  have hprod := mul_le_mul_of_nonneg_left
    (show (1 / 2 : ℝ) ≤ 1 - |s| by linarith) (show 0 ≤ 3 * |s|^3 by positivity)
  have hc : |s|^3 / (1 - |s|) ≤ 3 * |s|^3 := by
    apply (div_le_iff₀ hp).mpr
    nlinarith [show 0 ≤ |s|^3 by positivity]
  have hh := (abs_le.mp (h.trans hc)).1
  linarith

/-- The numerical event constraints in the final tensor step imply a strict
product threshold. This is a pointwise statement for any finite family d. -/
theorem exp_lt_product_of_event {ι : Type*} [Fintype ι]
    (d : ι → ℝ) (height variance : ℝ)
    (hd : ∀ i, |d i| ≤ 1/2)
    (hlin : height + variance / 2 + 2 ≤ ∑ i, d i)
    (hquad : ∑ i, (d i)^2 ≤ variance + 1)
    (hcub : 3 * ∑ i, |d i|^3 ≤ 1) :
    Real.exp height < ∏ i, (1 + d i) := by
  have hp (i : ι) : 0 < 1 + d i := by
    have h := (abs_le.mp (hd i)).1
    linarith
  have hpn : 0 < ∏ i, (1 + d i) := Finset.prod_pos (fun i _ => hp i)
  apply (Real.lt_log_iff_exp_lt hpn).mp
  rw [Real.log_prod (fun i _ => (hp i).ne')]
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset ι))
    (fun i _ => log_one_add_lower (hd i))
  simp only [Finset.sum_sub_distrib, div_eq_mul_inv, ← Finset.mul_sum,
    ← Finset.sum_mul] at hsum
  linarith

/-- The pointwise integer bound used in the two-term Bonferroni estimate,
written after multiplication by two. -/
theorem bonferroni_count (k : ℕ) :
    2 * (k : ℤ) - (k : ℤ) * ((k : ℤ) - 1) ≤ 2 * (if k = 0 then 0 else 1) := by
  rcases Nat.eq_zero_or_pos k with h | hp
  · simp [h]
  rw [ite_eq_right hp.ne']
  by_cases h2 : k = 1
  · norm_num [h2]
  have hk : (2 : ℤ) ≤ (k : ℤ) := by omega
  nlinarith [mul_nonneg (show 0 ≤ (k : ℤ) - 1 by linarith)
    (show 0 ≤ (k : ℤ) - 2 by linarith)]

end CenteredCube

#print axioms CenteredCube.log_one_add_lower
#print axioms CenteredCube.exp_lt_product_of_event
#print axioms CenteredCube.bonferroni_count
