import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

open Set MeasureTheory
open scoped BigOperators

namespace CubeSqrtProbability

/-- A single smooth Lindeberg replacement for two probability laws.  The affine and
quadratic moment contractions are arbitrary integrable functions.  The analytic
input is a pointwise remainder with an integrable nonnegative majorant. -/
theorem one_replacement_of_matching_moments
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure Ω') [IsProbabilityMeasure ν]
    (f l q a : Ω → ℝ) (g l' q' b : Ω' → ℝ) (c : ℝ)
    (hf : Integrable f μ) (hl : Integrable l μ) (hq : Integrable q μ)
    (ha : Integrable a μ) (hg : Integrable g ν) (hl' : Integrable l' ν)
    (hq' : Integrable q' ν) (hb : Integrable b ν)
    (hm₁ : ∫ x, l x ∂μ = ∫ y, l' y ∂ν)
    (hm₂ : ∫ x, q x ∂μ = ∫ y, q' y ∂ν)
    (hx : ∀ᵐ x ∂μ, |f x - (c + l x + q x)| ≤ a x)
    (hy : ∀ᵐ y ∂ν, |g y - (c + l' y + q' y)| ≤ b y) :
    |(∫ x, f x ∂μ) - (∫ y, g y ∂ν)| ≤ (∫ x, a x ∂μ) + ∫ y, b y ∂ν := by
  let F := fun x ↦ f x - (c + l x + q x)
  let G := fun y ↦ g y - (c + l' y + q' y)
  have hF : Integrable F μ := hf.sub (((integrable_const c).add hl).add hq)
  have hG : Integrable G ν := hg.sub (((integrable_const c).add hl').add hq')
  have hf' : (∫ x, F x ∂μ) = (∫ x, f x ∂μ) - (c + (∫ x, l x ∂μ) + ∫ x, q x ∂μ) := by
    change (∫ x, (f - (((fun _ : Ω ↦ c) + l) + q)) x ∂μ) = _
    rw [integral_sub' hf (((integrable_const c).add hl).add hq),
        integral_add' ((integrable_const c).add hl) hq, integral_add' (integrable_const c) hl]
    simp
  have hg' : (∫ y, G y ∂ν) = (∫ y, g y ∂ν) - (c + (∫ y, l' y ∂ν) + ∫ y, q' y ∂ν) := by
    change (∫ y, (g - (((fun _ : Ω' ↦ c) + l') + q')) y ∂ν) = _
    rw [integral_sub' hg (((integrable_const c).add hl').add hq'),
        integral_add' ((integrable_const c).add hl') hq', integral_add' (integrable_const c) hl']
    simp
  have he : (∫ x, f x ∂μ) - (∫ y, g y ∂ν) = (∫ x, F x ∂μ) - (∫ y, G y ∂ν) := by
    rw [hf', hg', hm₁, hm₂]
    ring
  rw [he]
  calc
    |(∫ x, F x ∂μ) - (∫ y, G y ∂ν)| ≤ |∫ x, F x ∂μ| + |∫ y, G y ∂ν| := abs_sub _ _
    _ ≤ (∫ x, |F x| ∂μ) + ∫ y, |G y| ∂ν :=
      add_le_add abs_integral_le_integral_abs abs_integral_le_integral_abs
    _ ≤ _ := add_le_add (integral_mono_ae hF.abs ha hx) (integral_mono_ae hG.abs hb hy)

/-- Sum the bounded changes along the progressively replaced row of an iid array.
Each step may have a different third-moment remainder. -/
theorem replacement_telescope (I : ℕ → ℝ) (e : ℕ → ℝ) (n : ℕ)
    (h : ∀ k < n, |I (k+1) - I k| ≤ e k) :
    |I n - I 0| ≤ ∑ k ∈ Finset.range n, e k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    calc
      |I (n+1) - I 0| = |(I n - I 0) + (I (n+1) - I n)| := by congr 1; ring
      _ ≤ |I n - I 0| + |I (n+1) - I n| := abs_add_le _ _
      _ ≤ _ := add_le_add (ih (fun k hk ↦ h k (Nat.lt_succ_of_lt hk))) (h n (Nat.lt_succ_self n))

/-- A uniform scalar replacement bound survives insertion of any common
independent background. The two laws can have different sample spaces. -/
theorem replacement_under_common_background
    {Z Ω Ω' : Type*} [MeasurableSpace Z] [MeasurableSpace Ω] [MeasurableSpace Ω']
    (ρ : Measure Z) [IsProbabilityMeasure ρ]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure Ω') [IsProbabilityMeasure ν]
    (f : Z × Ω → ℝ) (g : Z × Ω' → ℝ) (e : ℝ)
    (hf : Integrable f (ρ.prod μ)) (hg : Integrable g (ρ.prod ν))
    (h : ∀ᵐ z ∂ρ, |(∫ x, f (z,x) ∂μ) - ∫ y, g (z,y) ∂ν| ≤ e) :
    |(∫ x, f x ∂ρ.prod μ) - ∫ y, g y ∂ρ.prod ν| ≤ e := by
  rw [integral_prod f hf, integral_prod g hg,
      ← integral_sub hf.integral_prod_left hg.integral_prod_left]
  refine abs_integral_le_integral_abs.trans ?_
  have hInt := (hf.integral_prod_left.sub hg.integral_prod_left).abs
  simpa using integral_mono_ae hInt (integrable_const e) h

end CubeSqrtProbability
#print axioms CubeSqrtProbability.one_replacement_of_matching_moments
#print axioms CubeSqrtProbability.replacement_telescope
#print axioms CubeSqrtProbability.replacement_under_common_background
