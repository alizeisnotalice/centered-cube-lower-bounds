import BrownianExpectation
import Mathlib.MeasureTheory.Measure.Tilted
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
namespace CubeBrownian

theorem weighted_grid_lintegral_bound {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) (M G U : Ω → ℝ) (X : ι → Ω → ℝ)
    (hmM : Measurable M) (hmG : Measurable G) (hmU : Measurable U)
    (hmX : ∀ i, Measurable (X i)) (δ : ℝ) (hδ : 0 ≤ δ)
    (hgrid : ∀ᵐ w ∂μ, M w ≤ G w + U w ∧ ∃ i, G w = X i w)
    (hnorm : ∀ i, (∫ w, Real.exp (X i w) ∂μ) = 1) :
    (∫⁻ w, ENNReal.ofReal (Real.exp (M w)) ∂μ) ≤
      (∫⁻ w, ENNReal.ofReal (Real.exp (G w)) ∂μ) +
      ENNReal.ofReal (1-Real.exp (-δ)) * (∫⁻ w, ENNReal.ofReal (Real.exp (M w)) ∂μ) +
      ∑ i, ∫⁻ w in {w | δ < U w}, ENNReal.ofReal (Real.exp (U w)) ∂(μ.tilted (X i)) := by
  classical
  let S := {w | δ < U w}
  let a := ENNReal.ofReal (1-Real.exp (-δ))
  let m (w : Ω) := ENNReal.ofReal (Real.exp (M w))
  let g (w : Ω) := ENNReal.ofReal (Real.exp (G w))
  let u (w : Ω) := ENNReal.ofReal (Real.exp (U w))
  let p (i : ι) (w : Ω) := ENNReal.ofReal (Real.exp (X i w))
  let b (i : ι) (w : Ω) := S.indicator (fun w ↦ p i w * u w) w
  have hS : MeasurableSet S := measurableSet_lt measurable_const hmU
  have hmm : Measurable m := by dsimp [m]; fun_prop
  have hmg : Measurable g := by dsimp [g]; fun_prop
  have hmu : Measurable u := by dsimp [u]; fun_prop
  have hmp (i : ι) : Measurable (p i) := by dsimp [p]; fun_prop
  have hmb (i : ι) : Measurable (b i) := ((hmp i).mul hmu).indicator hS
  have hapos : 0 ≤ 1-Real.exp (-δ) := sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hδ))
  have hpw : ∀ᵐ w ∂μ, m w ≤ g w+a*m w+ ∑ i, b i w := by
    filter_upwards [hgrid] with w hw
    by_cases hs : w ∈ S
    · obtain ⟨i,hi⟩ := hw.2
      have hm : m w ≤ b i w := by
        rw [show b i w = p i w * u w from indicator_of_mem hs _]
        dsimp only [m,p,u]
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,← Real.exp_add]
        exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by simpa only [hi] using hw.1))
      have hs' : b i w ≤ ∑ j, b j w := Finset.single_le_sum (f := fun j ↦ b j w) (fun _ _ ↦ zero_le) (Finset.mem_univ i)
      exact hm.trans (hs'.trans (le_add_left (le_refl _)))
    · have hu : U w ≤ δ := le_of_not_gt hs
      have he : Real.exp (-δ)*Real.exp (M w) ≤ Real.exp (G w) := by
        rw [← Real.exp_add]
        exact Real.exp_le_exp.mpr (by linarith only [hw.1,hu])
      have hm : m w ≤ g w+a*m w := by
        dsimp only [m,g,a]
        rw [← ENNReal.ofReal_mul hapos,← ENNReal.ofReal_add (Real.exp_pos _).le (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        nlinarith only [he]
      exact hm.trans (le_add_right (le_refl _))
  have hI (i : ι) : (∫⁻ w, b i w ∂μ) = ∫⁻ w in S, u w ∂(μ.tilted (X i)) := by
    dsimp only [b]
    rw [lintegral_indicator hS]
    unfold Measure.tilted
    rw [hnorm i]
    simp only [div_one]
    exact (setLIntegral_withDensity_eq_setLIntegral_mul μ (hmp i) hmu hS).symm
  calc
    (∫⁻ w, m w ∂μ) ≤ ∫⁻ w, g w+a*m w+ ∑ i, b i w ∂μ := lintegral_mono_ae hpw
    _ = _ := by
      have hsm : Measurable (fun w ↦ g w + a*m w) := hmg.add (measurable_const.mul hmm)
      rw [lintegral_add_left hsm, lintegral_add_left hmg,lintegral_const_mul _ hmm,lintegral_finsetSum']
      · congr 1
        exact Finset.sum_congr rfl (fun i _ ↦ hI i)
      · exact fun i _ ↦ (hmb i).aemeasurable
end CubeBrownian
#print axioms CubeBrownian.weighted_grid_lintegral_bound
