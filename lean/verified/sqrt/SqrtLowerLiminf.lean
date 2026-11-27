import PaperScalarClosure
import SharpTruncationTransfer
import Mathlib.Topology.Instances.ENNReal.Lemmas

open Filter
open scoped ENNReal Topology

namespace CenteredCube

noncomputable def sqrtNormalizedWeakConstant (n : ℕ) : ℝ≥0∞ :=
  weakConstant n / ENNReal.ofReal (Real.sqrt (n:ℝ))

theorem coeff_le_sqrtNormalizedWeakConstant {n : ℕ} (hn : 0 < n) {b : ℝ} (hb : 0 ≤ b) :
    ENNReal.ofReal (b*Real.sqrt (n:ℝ)) ≤ weakConstant n ↔
      ENNReal.ofReal b ≤ sqrtNormalizedWeakConstant n := by
  have hp : 0 < Real.sqrt (n:ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
  rw [sqrtNormalizedWeakConstant, ENNReal.ofReal_mul hb,
    ENNReal.le_div_iff_mul_le (Or.inl (ne_of_gt (ENNReal.ofReal_pos.mpr hp)))
      (Or.inl ENNReal.ofReal_ne_top)]

theorem sqrtNormalizedWeakConstant_liminf_ge {c : ℝ} (hc : 0 < c)
    (H : ∀ b : ℝ, 0 < b → b < c →
      ∀ᶠ n : ℕ in atTop, ENNReal.ofReal (b*Real.sqrt (n:ℝ)) ≤ weakConstant n) :
    ENNReal.ofReal c ≤ liminf sqrtNormalizedWeakConstant atTop := by
  rw [Filter.le_liminf_iff']
  intro y hy
  have hyne : y ≠ ⊤ := ne_top_of_lt hy
  have hb : y.toReal < c := by
    have := ENNReal.toReal_lt_toReal hyne ENNReal.ofReal_ne_top |>.mpr hy
    rwa [ENNReal.toReal_ofReal hc.le] at this
  obtain ⟨b, hyb, hbc⟩ := exists_between hb
  have hb0 : 0 < b := ENNReal.toReal_nonneg.trans_lt hyb
  filter_upwards [H b hb0 hbc, eventually_gt_atTop (0 : ℕ)] with n hn hn0
  have h := (coeff_le_sqrtNormalizedWeakConstant hn0 hb0.le).1 hn
  exact (show y ≤ ENNReal.ofReal b by
    rw [← ENNReal.ofReal_toReal hyne]
    exact ENNReal.ofReal_le_ofReal hyb.le).trans h

theorem eventually_strict_sqrt_of_liminf {c b : ℝ} (hb : 0 < b) (hbc : b < c)
    (hc : ENNReal.ofReal c ≤ liminf sqrtNormalizedWeakConstant atTop) :
    ∀ᶠ n : ℕ in atTop, ENNReal.ofReal (b*Real.sqrt (n:ℝ)) < weakConstant n := by
  have he := eventually_lt_of_lt_liminf (show ENNReal.ofReal b < liminf sqrtNormalizedWeakConstant atTop from
    ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg hb.le).2 hbc).trans_le hc)
  filter_upwards [he, eventually_gt_atTop (0 : ℕ)] with n hn hn0
  have hp : 0 < Real.sqrt (n:ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn0)
  unfold sqrtNormalizedWeakConstant at hn
  rw [ENNReal.ofReal_mul hb.le]
  exact (ENNReal.lt_div_iff_mul_lt (Or.inl (ne_of_gt (ENNReal.ofReal_pos.mpr hp)))
    (Or.inl ENNReal.ofReal_ne_top)).1 hn

theorem eventually_one_thirty_fifth_of_exact_liminf
    (h : ENNReal.ofReal CubeSqrtEnd.paperConstant ≤ liminf sqrtNormalizedWeakConstant atTop) :
    ∀ᶠ n : ℕ in atTop, ENNReal.ofReal (Real.sqrt (n:ℝ)/35) < weakConstant n := by
  have H := eventually_strict_sqrt_of_liminf (b := (1:ℝ)/35) (by norm_num)
    CubeSqrtEnd.paperConstant_gt_rational h
  simpa only [one_div, div_eq_mul_inv, one_mul, mul_comm] using H

/-- A lower bound on the untruncated normalized probability transfers to the
original weak constant with the same strict limiting coefficient. -/
theorem sqrtWeakConstant_eventually_of_normalized_tail
    (A : ℕ → ℝ) {b b' : ℝ} (hb : 0 < b) (hbb : b < b')
    (hA : ∀ᶠ n : ℕ in atTop, b' ≤ A n)
    (hW : ∀ᶠ n : ℕ in atTop,
      ENNReal.ofReal (A n * (1 - 1 / (n:ℝ)^2)^n * Real.sqrt (n:ℝ)) ≤ weakConstant n) :
    ∀ᶠ n : ℕ in atTop, ENNReal.ofReal (b*Real.sqrt (n:ℝ)) ≤ weakConstant n := by
  have hb' : 0 ≤ b' := (hb.trans hbb).le
  have hT : Tendsto (fun n : ℕ => b'*(1 - 1 / (n:ℝ)^2)^n) atTop (𝓝 b') := by
    simpa only [mul_one] using truncation_retention_tendsto.const_mul b'
  have hlt : ∀ᶠ n : ℕ in atTop, b < b'*(1 - 1 / (n:ℝ)^2)^n := hT.eventually (lt_mem_nhds hbb)
  filter_upwards [hA,hW,hlt,eventually_ge_atTop (1:ℕ)] with n hnA hnW hnl hn
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hf : 0 ≤ (1 - 1 / (n:ℝ)^2)^n := by
    exact pow_nonneg (sub_nonneg.2 ((div_le_one (by positivity)).2 (by nlinarith))) _
  refine (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _))).trans hnW
  exact hnl.le.trans (mul_le_mul_of_nonneg_right hnA hf)

#print axioms sqrtWeakConstant_eventually_of_normalized_tail

#print axioms sqrtNormalizedWeakConstant_liminf_ge
#print axioms eventually_one_thirty_fifth_of_exact_liminf
end CenteredCube
