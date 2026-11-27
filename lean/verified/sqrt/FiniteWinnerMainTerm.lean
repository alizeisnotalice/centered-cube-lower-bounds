import ActualWinnerWeight
import IsonormalWinnerLimitLaw
import BrownianExpectation
import Mathlib.Topology.Algebra.Monoid

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology ProbabilityTheory
namespace CubeBrownian

/-- Final finite-winner assembly. The actual strict exceedance, tie-breaking,
finite sum, and canonical target expectation are all exact. The only inputs
are the verified coordinate winner thin-layer limits and the asymptotically
negligible comparison error for each weighted winner. -/
theorem finiteWinner_exceedance_main_term
    {Ω : ℕ → Type*} {Ω' H : Type*} [∀ n, MeasurableSpace (Ω n)] [MeasurableSpace Ω']
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (μ : (n : ℕ) → Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (ν : Measure Ω') [IsProbabilityMeasure ν]
    {N : ℕ} (hN : 0 < N) (X : (n : ℕ) → Fin N → Ω n → ℝ)
    (hm : ∀ n i, Measurable (X n i))
    (hInt : ∀ n i, Integrable (fun w ↦ Real.exp (X n i w)) (μ n))
    (hNorm : ∀ n i, ∫ w, Real.exp (X n i w) ∂(μ n) = 1)
    (h u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n)
    (W : H →ₗ[ℝ] (Ω' → ℝ)) (hmW : ∀ x, Measurable (W x))
    (hW : ∀ x, HasLaw (W x) (gaussianReal 0 (isoVar 1 x)) ν)
    (k : ℝ≥0) (f : Fin N → H)
    (γ ε : ℕ → Fin N → ℝ)
    (hGaussian : ∀ j, Tendsto (fun n ↦ u n * γ n j) atTop
      (𝓝 (φ 0 * (ν.map (fun w i ↦ isoScore W k (f i-f j) w)).real (winnerDifferenceFace j))))
    (hError : ∀ j, ∀ᶠ n in atTop,
      |winnerFaceWeight ((μ n).tilted (X n j)) (fun w ↦ X n j w-h n)
        (fun w i ↦ X n i w-X n j w) (winnerDifferenceFace j) - γ n j| ≤ ε n j)
    (hRate : ∀ j, Tendsto (fun n ↦ u n * ε n j) atTop (𝓝 0)) :
    Tendsto (fun n ↦ u n * Real.exp (h n) * (μ n).real {w | h n < ⨆ i, X n i w}) atTop
      (𝓝 (φ 0 * (∫ w, Real.exp (⨆ i, isoScore W k (f i) w) ∂ν))) := by
  classical
  let A (n : ℕ) (j : Fin N) := winnerFaceWeight ((μ n).tilted (X n j))
    (fun w ↦ X n j w-h n) (fun w i ↦ X n i w-X n j w) (winnerDifferenceFace j)
  let G (j : Fin N) : Ω' → Fin N → ℝ := fun w i ↦ isoScore W k (f i-f j) w
  let P (j : Fin N) := (ν.map (G j)).real (winnerDifferenceFace j)
  have hOne (j : Fin N) : Tendsto (fun n ↦ u n * A n j) atTop (𝓝 (φ 0 * P j)) := by
    have hDiff : Tendsto (fun n ↦ u n*(A n j-γ n j)) atTop (𝓝 0) := by
      apply squeeze_zero_norm' _ (hRate j)
      filter_upwards [hError j] with n hn
      rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (hu n)]
      exact mul_le_mul_of_nonneg_left hn (hu n)
    have hh := (hGaussian j).add hDiff
    apply (show Tendsto (fun n ↦ u n*γ n j + u n*(A n j-γ n j)) atTop (𝓝 (φ 0*P j)) by
      simpa only [zero_add,add_zero] using hh).congr
    intro n
    ring
  have hSum : Tendsto (fun n ↦ ∑ j, u n*A n j) atTop (𝓝 (∑ j, φ 0*P j)) :=
    tendsto_finsetSum _ (fun j _ ↦ hOne j)
  have hPfinite (j : Fin N) : (ν.map (G j)) (winnerDifferenceFace j) ≠ ∞ := by
    have hmG : Measurable (G j) := Measurable.of_eval fun i ↦
      (measurable_const.mul (hmW (f i-f j))).sub_const _
    let _ : IsProbabilityMeasure (ν.map (G j)) :=
      (Measure.isProbabilityMeasure_map_iff hmG.aemeasurable).2 inferInstance
    exact measure_ne_top _ _
  have hCanon := congrArg ENNReal.toReal (isonormal_winner_face_sum_expMax ν W hmW hW k hN f)
  rw [ENNReal.toReal_sum (fun j _ ↦ hPfinite j)] at hCanon
  have hMeas : Measurable (fun w ↦ Real.exp (⨆ i, isoScore W k (f i) w)) :=
    Real.measurable_exp.comp (Measurable.iSup fun i ↦
      (measurable_const.mul (hmW (f i))).sub_const _)
  have hReal : (∫ w, Real.exp (⨆ i, isoScore W k (f i) w) ∂ν) =
      (∫⁻ w, ENNReal.ofReal (Real.exp (⨆ i, isoScore W k (f i) w)) ∂ν).toReal :=
    integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall fun w ↦ (Real.exp_pos (⨆ i, isoScore W k (f i) w)).le)
    hMeas.aestronglyMeasurable
  rw [← hReal] at hCanon
  have hC : (∑ j, φ 0*P j) = φ 0 * (∫ w, Real.exp (⨆ i, isoScore W k (f i) w) ∂ν) := by
    rw [← Finset.mul_sum]
    exact congrArg (fun x ↦ φ 0*x) hCanon
  rw [hC] at hSum
  apply hSum.congr
  intro n
  rw [← Finset.mul_sum,mul_assoc,
    finiteWinner_exceedance_eq_sum_faceWeight (μ n) hN (X n) (hm n) (hInt n) (hNorm n) (h n)]

end CubeBrownian
#print axioms CubeBrownian.finiteWinner_exceedance_main_term
