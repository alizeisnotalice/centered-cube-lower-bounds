/-
Model lock for the centred-cube lower bounds.

The manuscripts define, for `f ∈ L¹(ℝⁿ)` and `λ > 0`,

  `M_n f (x) = sup_{L>0} |x + [-L/2,L/2]ⁿ|⁻¹ ∫_{x+[-L/2,L/2]ⁿ} |f|`,

and `C_n` as the supremum of `λ |{M_n f > λ}| / ‖f‖₁` over `f ≠ 0` and `λ > 0`
(equation (1.1) of the `√n` manuscript, equation (1) of the `√n/log n` manuscript).

`Cubes.lean` already fixes exactly these objects (`cube`, `cubeAverage`, `maximal`,
`weakConstant`).  This file records the identification:

* `paperWeakConstant` is the same sup written as a sup over *pairs* `(f, λ)`,
  and equals `weakConstant` (`paperWeakConstant_eq`);
* the universal property `a ≤ C_n ↔ ∀ f λ, a ≤ λ|{M_n f > λ}|/‖f‖₁`
  (`le_weakConstant_iff`) and its dual (`weakConstant_le_iff`) are what every
  lower-bound argument uses;
* the truncated maximal operator `sup_{0<r≤r_max}` used by the manuscripts'
  transfer lemma has level sets inside those of `M_n`, so its ratios are also
  bounded by `C_n` (`weakRatio_trunc_le`).

Nothing here restricts `C_n` to a periodic model, a lattice model, or a
scale-restricted constant: the only constant mentioned is `weakConstant`.
-/
import Cubes

open Set MeasureTheory
open scoped ENNReal NNReal

namespace CenteredCube

/-! ### The manuscript's defining supremum -/

/-- Integrable functions of positive `L¹` mass: the admissible numerators of (1.1). -/
abbrev Admissible (n : ℕ) : Type :=
  {f : Space n → ℝ // Integrable f volume ∧ 0 < absMass f}

/-- Positive thresholds.  This is definitionally the index type of `weakConstant`. -/
abbrev Positive : Type := Ioi (0 : ℝ)

/-- Definition (1.1): the supremum of `λ |{M_n f > λ}| / ‖f‖₁` over pairs `(f, λ)`
with `f` integrable of positive mass and `λ > 0`. -/
noncomputable def paperWeakConstant (n : ℕ) : ℝ≥0∞ :=
  ⨆ p : Admissible n × Positive, weakRatio p.1.val p.2.val

/-- The pair-indexed supremum of (1.1) is the iterated supremum `weakConstant`. -/
theorem paperWeakConstant_eq (n : ℕ) : paperWeakConstant n = weakConstant n := by
  unfold paperWeakConstant weakConstant
  refine le_antisymm ?_ ?_
  · refine iSup_le ?_
    rintro ⟨⟨f, hf, hm⟩, ⟨t, ht⟩⟩
    exact le_iSup_of_le (⟨f, hf, hm⟩ : Admissible n)
      (le_iSup_of_le (⟨t, ht⟩ : Positive) le_rfl)
  · refine iSup_le ?_
    rintro ⟨f, hf, hm⟩
    refine iSup_le ?_
    rintro ⟨t, ht⟩
    exact le_iSup_of_le (⟨⟨f, hf, hm⟩, ⟨t, ht⟩⟩ : Admissible n × Positive) le_rfl

/-- `C_n` is an upper bound for every admissible ratio. -/
theorem weakRatio_le_weakConstant {n : ℕ} (f : Space n → ℝ) (hf : Integrable f volume)
    (hm : 0 < absMass f) {t : ℝ} (ht : 0 < t) : weakRatio f t ≤ weakConstant n :=
  weakRatio_le_constant f hf hm ht

/-- `C_n` is the *least* upper bound: `C_n ≤ a` iff every admissible ratio is `≤ a`. -/
theorem weakConstant_le_iff {n : ℕ} {a : ℝ≥0∞} :
    weakConstant n ≤ a ↔
      ∀ (f : Space n → ℝ), Integrable f volume → 0 < absMass f → ∀ t : ℝ, 0 < t →
        weakRatio f t ≤ a := by
  constructor
  · intro h f hf hm t ht
    exact (weakRatio_le_weakConstant f hf hm ht).trans h
  · intro h
    unfold weakConstant
    refine iSup_le ?_
    rintro ⟨f, hf, hm⟩
    refine iSup_le ?_
    rintro ⟨t, ht⟩
    exact h f hf hm t ht

/-- `a ≤ C_n` iff every `b < a` is exceeded by some admissible ratio. -/
theorem le_weakConstant_iff {n : ℕ} {a : ℝ≥0∞} :
    a ≤ weakConstant n ↔
      ∀ b : ℝ≥0∞, b < a → ∃ (f : Space n → ℝ) (t : ℝ),
        Integrable f volume ∧ 0 < absMass f ∧ 0 < t ∧ b < weakRatio f t := by
  constructor
  · intro h b hb
    by_contra hcon
    have hle : weakConstant n ≤ b := by
      rw [weakConstant_le_iff]
      intro f hf hm t ht
      exact not_lt.mp fun hlt => hcon ⟨f, t, hf, hm, ht, hlt⟩
    exact absurd (hle.trans_lt hb) (not_lt.mpr h)
  · intro h
    by_contra hcon
    have hlt : weakConstant n < a := not_le.mp hcon
    obtain ⟨f, t, hf, hm, ht, hft⟩ := h _ hlt
    exact absurd (weakRatio_le_weakConstant f hf hm ht) (not_le.mpr hft)

/-- Every value strictly below `C_n` is exceeded by some admissible ratio. -/
theorem exists_weakRatio_gt {n : ℕ} {a : ℝ≥0∞} (h : a < weakConstant n) :
    ∃ (f : Space n → ℝ) (t : ℝ),
      Integrable f volume ∧ 0 < absMass f ∧ 0 < t ∧ a < weakRatio f t :=
  (le_weakConstant_iff.mp le_rfl) a h

/-! ### The truncated maximal operator used in the transfer lemma -/

/-- `sup` of the centred cube averages over side lengths `0 < r ≤ rmax`. -/
noncomputable def maximalTrunc {n : ℕ} (f : Space n → ℝ) (x : Space n) (rmax : ℝ) :
    ℝ≥0∞ :=
  ⨆ r : Ioc (0 : ℝ) rmax, cubeAverage f x r

/-- Truncating the scale range only lowers the maximal operator. -/
theorem maximalTrunc_le_maximal {n : ℕ} (f : Space n → ℝ) (x : Space n) {rmax : ℝ} :
    maximalTrunc f x rmax ≤ maximal f x :=
  iSup_le fun r => average_le_maximal f x r.2.1

/-- Therefore the level set of the truncated operator is contained in that of `M_n`. -/
theorem levelSet_trunc_subset {n : ℕ} (f : Space n → ℝ) (rmax t : ℝ) :
    {x | ENNReal.ofReal t < maximalTrunc f x rmax} ⊆
      {x | ENNReal.ofReal t < maximal f x} :=
  fun _ hx => hx.trans_le (maximalTrunc_le_maximal f _)

/-- A ratio computed with the truncated maximal operator is still bounded by `C_n`;
this is the form in which the manuscripts' transfer lemma feeds the lower bound. -/
theorem weakRatio_trunc_le {n : ℕ} (f : Space n → ℝ) (hf : Integrable f volume)
    (hm : 0 < absMass f) {t : ℝ} (ht : 0 < t) (rmax : ℝ) :
    ENNReal.ofReal t * volume {x | ENNReal.ofReal t < maximalTrunc f x rmax} / absMass f ≤
      weakConstant n := by
  have hmono : volume {x | ENNReal.ofReal t < maximalTrunc f x rmax} ≤
      volume {x | ENNReal.ofReal t < maximal f x} :=
    measure_mono (levelSet_trunc_subset f rmax t)
  calc ENNReal.ofReal t * volume {x | ENNReal.ofReal t < maximalTrunc f x rmax} / absMass f
      ≤ ENNReal.ofReal t * volume {x | ENNReal.ofReal t < maximal f x} / absMass f := by
        gcongr
    _ = weakRatio f t := rfl
    _ ≤ weakConstant n := weakRatio_le_constant f hf hm ht

/-! ### Real-valued reading of an `ℝ≥0∞` lower bound -/

/-- A finite weak constant can be read as a real number: an `ofReal` lower bound
is exactly the corresponding real inequality.  Both manuscripts state their
theorems for the real number `C_n`; this lemma is the translation. -/
theorem ofReal_le_weakConstant_iff {n : ℕ} {a : ℝ} (ha : 0 ≤ a) (hfin : weakConstant n ≠ ∞) :
    ENNReal.ofReal a ≤ weakConstant n ↔ a ≤ (weakConstant n).toReal := by
  constructor
  · intro h
    simpa [ENNReal.toReal_ofReal ha] using ENNReal.toReal_mono hfin h
  · intro h
    calc ENNReal.ofReal a ≤ ENNReal.ofReal (weakConstant n).toReal := ENNReal.ofReal_le_ofReal h
      _ = weakConstant n := ENNReal.ofReal_toReal hfin

end CenteredCube

#print axioms CenteredCube.paperWeakConstant_eq
#print axioms CenteredCube.weakConstant_le_iff
#print axioms CenteredCube.le_weakConstant_iff
#print axioms CenteredCube.exists_weakRatio_gt
#print axioms CenteredCube.maximalTrunc_le_maximal
#print axioms CenteredCube.weakRatio_trunc_le
#print axioms CenteredCube.ofReal_le_weakConstant_iff
