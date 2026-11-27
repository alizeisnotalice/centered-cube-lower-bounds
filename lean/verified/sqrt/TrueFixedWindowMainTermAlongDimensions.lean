import ActualFacetNondegenerateAlongDimensions
import TrueWinnerWeightAsymptoticAlongDimensions

open MeasureTheory ProbabilityTheory Filter WithLp CubeBrownian Set
open scoped NNReal ENNReal Topology ProbabilityTheory BigOperators
namespace CubeSqrtProbability

/-- The fixed-window main term for the actual iid log-product score.
Hypotheses are solely the explicit source/scale asymptotics and the
geometry's raw L² node distances. All Esscher, iid, Gaussian projected
moment, finite-facet, rate, and union steps are discharged. -/
theorem true_fixed_window_exceedance_main_term_along_dimensions
    {Ω Ω' H : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {N : ℕ} (hN : 0<N) (dim : ℕ → ℕ) (hDim : Tendsto dim atTop atTop) (d : Fin N → ℕ → Ω → ℝ) (a v h : ℕ → ℝ)
    (hm : ∀ i n, Measurable (d i n))
    (ha0 : ∀ n, 0 ≤ a n) (ha : ∀ n, a n ≤ 1/2) (hb : ∀ i n w, |d i n w|≤a n)
    (hZero : ∀ i n, (∫ w, d i n w ∂P)=0)
    (haLim : Tendsto a atTop (𝓝 0)) (hV : Tendsto v atTop atTop)
    (hSmall : ∀ i, Tendsto (fun n : ℕ ↦ (dim n:ℝ)*a n*rawSq P (d i n)) atTop (𝓝 0))
    (hSqZero : ∀ i, Tendsto (fun n ↦ rawSq P (d i n)) atTop (𝓝 0))
    (hQSq : ∀ i, Tendsto (fun n : ℕ ↦ ((dim n:ℝ)*rawSq P (d i n))^2/(dim n:ℝ)) atTop (𝓝 0))
    (E : ℝ) (hQ : ∀ᶠ n : ℕ in atTop, ∀ i, |(dim n:ℝ)*rawSq P (d i n)-v n|≤E)
    (A : ℝ) (hh : ∀ᶠ n : ℕ in atTop, |v n/2-h n|≤A)
    (M : ℝ) (hM : 0≤M) (hvlog : ∀ᶠ n : ℕ in atTop, 0≤v n ∧ v n≤M*Real.log (dim n:ℝ))
    (C : ℝ) (hC : 0≤C) (hampl : ∀ᶠ n : ℕ in atTop, 8*a n≤C*(√(v n)*(dim n:ℝ)^(-(1/2:ℝ))))
    (ν : Measure Ω') [IsProbabilityMeasure ν]
    (W : H →ₗ[ℝ] (Ω' → ℝ)) (hmW : ∀ x, Measurable (W x))
    (hW : ∀ x, HasLaw (W x) (gaussianReal 0 (isoVar 1 x)) ν)
    {k : ℝ≥0} (hk : 0<k) (f : Fin N → H) (hf : Function.Injective f)
    (hDist : ∀ i t, Tendsto (fun n : ℕ ↦ (dim n:ℝ)*rawSq P (fun w ↦ d i n w-d t n w))
      atTop (𝓝 ((k:ℝ)*‖f i-f t‖^2))) :
    let X (n : ℕ) (j : Fin N) (w : Fin (dim n) → Ω) := ∑ c, Real.log (1+d j n (w c))
    let μ (n : ℕ) := Measure.pi (fun _ : Fin (dim n) ↦ P)
    Tendsto (fun n ↦ √(v n)*Real.exp (h n)*(μ n).real {w | h n < ⨆ i, X n i w})
      atTop (𝓝 (φ 0 * (∫ w, Real.exp (⨆ i, isoScore W k (f i) w) ∂ν))) := by
  classical
  dsimp only
  let μ (n : ℕ) := Measure.pi (fun _ : Fin (dim n) ↦ P)
  letI : ∀ n, IsProbabilityMeasure (μ n) := fun n ↦ inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _ : Fin (dim n) ↦ P)))
  let X (n : ℕ) (j : Fin N) (w : Fin (dim n) → Ω) := ∑ c, Real.log (1+d j n (w c))
  let G (n : ℕ) := trueLogScores (fun i ↦ d i n)
  let Q (n : ℕ) (j : Fin N) := winnerTilt P (d j n)
  have hmX (n : ℕ) (i : Fin N) : Measurable (X n i) :=
    Finset.measurable_sum _ (fun c _ ↦ Real.measurable_log.comp
      (measurable_const.add ((hm i n).comp (measurable_pi_apply c))))
  have hInt (n : ℕ) (i : Fin N) : Integrable (fun w ↦ Real.exp (X n i w)) (μ n) := by
    apply integrable_of_uniform_abs (μ n) (Real.measurable_exp.comp (hmX n i)) (B:=(3/2:ℝ)^dim n)
    intro w
    unfold X
    rw [Function.comp_apply,abs_of_nonneg (Real.exp_nonneg _),Real.exp_sum]
    calc
      _ ≤ ∏ _ : Fin (dim n), (3/2:ℝ) := Finset.prod_le_prod₀ (fun c _ ↦ Real.exp_nonneg _)
        (fun c _ ↦ by rw [exp_logPerturbation_eq (ha n) (hb i n (w c))]; linarith [(abs_le.mp (hb i n (w c))).2,ha n])
      _ = _ := by simp [div_pow]
  have hNorm (n : ℕ) (i : Fin N) : ∫ w, Real.exp (X n i w) ∂μ n = 1 := by
    unfold X μ
    simp_rw [Real.exp_sum]
    rw [integral_fintype_prod_eq_pow (ι:=Fin (dim n)) (μ:=P) (fun w ↦ Real.exp (Real.log (1+d i n w)))]
    have h1 : (∫ w, Real.exp (Real.log (1+d i n w)) ∂P)=1 := by
      simp_rw [show ∀ w, Real.exp (Real.log (1+d i n w))=1+d i n w from
        fun w ↦ exp_logPerturbation_eq (ha n) (hb i n w)]
      rw [integral_add (integrable_const _) (integrable_of_uniform_abs P (hm i n) (hb i n)),hZero i n]
      simp
    rw [h1,one_pow]
  let γ (n : ℕ) (j : Fin N) := winnerFaceWeight (trueWinnerGaussian (Q n j) j (G n) (dim n))
    (trueWinnerGaussianAnchor (Q n j) j (G n) (dim n) (h n)) (trueWinnerGaussianRelative (Q n j) j (G n) (dim n))
    (WithLp.ofLp ⁻¹' winnerDifferenceFace j)
  let α (n : ℕ) (j : Fin N) := winnerFaceWeight ((μ n).tilted (X n j))
    (fun w ↦ X n j w-h n) (fun w i ↦ X n i w-X n j w) (winnerDifferenceFace j)
  refine finiteWinner_exceedance_main_term (Ω := fun n ↦ Fin (dim n) → Ω) μ ν hN X hmX hInt hNorm h (fun n ↦ √(v n))
    (fun _ ↦ Real.sqrt_nonneg _) W hmW hW k f γ (fun n j ↦ |α n j-γ n j|) ?_ ?_ ?_
  · intro j
    exact true_esscher_gaussian_winner_limit_along_dimensions P j dim hDim d a v h hm ha0 ha hb hZero haLim hV
      hSmall (hSqZero j) (hQSq j) E hQ A hh ν W hmW hW hk f hf hDist
  · intro j
    exact Eventually.of_forall fun n ↦ le_rfl
  · intro j
    obtain ⟨c,hc,hDiag⟩ := actual_winner_facet_nondegenerate_along_dimensions P j dim hDim d a v hm ha0 ha hb hZero haLim hV
      hSmall (hQSq j) E (hQ.mono fun n hn ↦ hn j) hk f hf hDist
    have hErr : Tendsto (fun n ↦ √(v n)*(α n j-γ n j)) atTop (𝓝 0) :=
      true_winner_weight_difference_tendsto_along_dimensions P j dim hDim (fun n i ↦ d i n) a v h (fun n i ↦ hm i n)
        ha0 ha (fun n i ↦ hb i n) M hM hvlog C hC hampl c hc hDiag
    simpa only [abs_mul,abs_zero,abs_of_nonneg (Real.sqrt_nonneg _)] using hErr.abs

end CubeSqrtProbability
#print axioms CubeSqrtProbability.true_fixed_window_exceedance_main_term_along_dimensions
