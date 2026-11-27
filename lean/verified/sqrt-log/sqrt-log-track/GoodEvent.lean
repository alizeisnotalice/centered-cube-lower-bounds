import Mathlib.Probability.Moments.SubGaussian
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
namespace CubeMD

/-- The exact paper truncation event, parameterized by the standardized
row and its physical variance multiplier. -/
def quadraticGood {Ω : Type*} {n : ℕ} (Y : Ω → ℝ) (σ u : ℝ) :
    Set (Fin n → Ω) := {w | σ^2 * (∑ i, Y (w i)^2) ≤ u^2 + 1}

theorem quadraticGood_compl_eq {Ω : Type*} {n : ℕ} (Y : Ω → ℝ)
    (σ u : ℝ) (hn : 0 < n) (hu : 0 < u) (hσ : σ^2 = u^2 / (n:ℝ)) :
    (quadraticGood (n := n) Y σ u)ᶜ =
      {w | (n:ℝ)/u^2 < ∑ i, (Y (w i)^2 - 1)} := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hu2 : 0 < u^2 := sq_pos_of_pos hu
  ext w
  change ¬ σ^2 * (∑ i, Y (w i)^2) ≤ u^2 + 1 ↔ _
  rw [not_le, hσ]
  simp only [mem_setOf_eq, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  rw [div_mul_eq_mul_div, lt_div_iff₀ hn']
  constructor
  · intro h
    apply (div_lt_iff₀ hu2).2
    nlinarith only [h]
  · intro h
    have h' := (div_lt_iff₀ hu2).mp h
    nlinarith only [h']

/-- Hoeffding gives a sufficient, slightly stronger than the manuscript's
Bernstein bound with its coarse variance envelope, estimate for Gᶜ. -/
theorem quadraticGood_bad_probability {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {n : ℕ} (hn : 0 < n) (Y : Ω → ℝ) (hY : Measurable Y)
    (B : ℝ) (hB : 0 ≤ B) (hb : ∀ᵐ x ∂μ, |Y x| ≤ B)
    (hmean : (∫ x, Y x^2 ∂μ) = 1)
    (σ u : ℝ) (hu : 0 < u) (hσ : σ^2 = u^2 / (n:ℝ)) :
    (Measure.pi (fun _ : Fin n ↦ μ)).real (quadraticGood (n := n) Y σ u)ᶜ ≤
      Real.exp (-( (n:ℝ) / (2 * (B^2+1)^2 * u^4))) := by
  let P := Measure.pi (fun _ : Fin n ↦ μ)
  let b := B^2 + 1
  let W : Ω → ℝ := fun v ↦ Y v^2 - 1
  let Z : Fin n → (Fin n → Ω) → ℝ := fun i w ↦ W (w i)
  have hb' : 0 < b := by dsimp only [b]; positivity
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hW : Measurable W := (hY.pow_const _).sub_const _
  have hi : iIndepFun Z P := iIndepFun_pi (μ := fun _ : Fin n ↦ μ) (fun _ ↦ hW.aemeasurable)
  have he (i : Fin n) : MeasurePreserving (fun w : Fin n → Ω ↦ w i) P μ :=
    measurePreserving_eval (fun _ : Fin n ↦ μ) i
  have hYInt : Integrable (fun x ↦ Y x^2) μ := by
    apply (integrable_const (B^2)).mono' (hY.pow_const 2).aestronglyMeasurable
    filter_upwards [hb] with x hx
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) hx _
  have hWmean : (∫ x, W x ∂μ) = 0 := by
    dsimp only [W]
    rw [integral_sub hYInt (integrable_const _), hmean]
    simp
  have hWb : ∀ᵐ x ∂μ, W x ∈ Icc (-b) b := by
    filter_upwards [hb] with x hx
    have hs : Y x^2 ≤ B^2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hx _
    change -b ≤ Y x^2-1 ∧ Y x^2-1 ≤ b
    dsimp only [b]
    constructor <;> nlinarith only [hs, sq_nonneg (Y x), sq_nonneg B]
  let bNN : ℝ≥0 := ⟨b, hb'.le⟩
  have hsg (i : Fin n) : HasSubgaussianMGF (Z i) (bNN^2) P := by
    have hh : ∀ᵐ w ∂P, Z i w ∈ Icc (-b) b :=
      (he i).quasiMeasurePreserving.ae hWb
    have hm : (∫ w, Z i w ∂P) = 0 := by
      have e : (∫ w, Z i w ∂P) = ∫ v, W v ∂μ :=
        integral_comp_eval (μ := fun _ : Fin n ↦ μ) (i := i) (f := W) hW.aestronglyMeasurable
      exact e.trans hWmean
    have hp : Measurable (Z i) := hW.comp (he i).measurable
    have hpar : ‖b - (-b)‖₊ / 2 = bNN := by
      apply NNReal.eq
      change ‖b - (-b)‖ / 2 = b
      rw [Real.norm_eq_abs]
      rw [abs_of_nonneg (by linarith only [hb'.le])]
      change (b - -b) / 2 = b
      ring
    rw [← hpar]
    exact hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero hp.aemeasurable hh hm
  let ε := (n:ℝ)/u^2
  have hH := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hi
    (c := fun _ ↦ bNN^2) (s := Finset.univ) (fun i _ ↦ hsg i)
    (ε := ε) (by dsimp only [ε]; positivity)
  have heq : -ε^2 / (2 * ((∑ _i : Fin n, bNN^2 : ℝ≥0) : ℝ)) =
      -( (n:ℝ) / (2*b^2*u^4)) := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, NNReal.coe_pow, NNReal.coe_mul, NNReal.coe_natCast]
    change -((n:ℝ)/u^2)^2 / (2*((n:ℝ)*b^2)) = _
    field_simp [hn'.ne', hu.ne', hb'.ne'] <;> ring
  rw [heq] at hH
  rw [quadraticGood_compl_eq Y σ u hn hu hσ]
  have hsub : {w : Fin n → Ω | (n:ℝ)/u^2 < ∑ i, (Y (w i)^2-1)} ⊆
      {w : Fin n → Ω | ε ≤ ∑ i, Z i w} := by
    intro w hw
    change (n:ℝ)/u^2 < ∑ i, (Y (w i)^2-1) at hw
    exact hw.le
  exact (measureReal_mono (μ := P) hsub).trans hH

end CubeMD
#print axioms CubeMD.quadraticGood_compl_eq
#print axioms CubeMD.quadraticGood_bad_probability
