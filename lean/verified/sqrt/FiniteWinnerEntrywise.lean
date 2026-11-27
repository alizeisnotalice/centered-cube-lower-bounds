import FiniteWinnerProjectionGlue

open MeasureTheory ProbabilityTheory Filter Set WithLp CubeBrownian
open scoped NNReal ENNReal Topology ProbabilityTheory RealInnerProductSpace
namespace CubeSqrtProbability

/-- Interface to the fixed-winner weighted Gaussian limit using only
coordinatewise means/covariances. In particular the regression vector
and all projected moment hypotheses are constructed, not assumed. -/
theorem finite_winner_limit_of_entrywise
    {Ω Ω' H : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {N : ℕ} (j : Fin N) (μ : ℕ → Measure Ω) (ν : Measure Ω')
    [∀ n, IsProbabilityMeasure (μ n)] [IsProbabilityMeasure ν]
    (Z : ℕ → Ω → ℝ) (D : ℕ → Ω → EuclideanSpace ℝ (Fin N))
    (hmZ : ∀ n, Measurable (Z n)) (hmD : ∀ n, Measurable (D n))
    (hZD : ∀ n, HasGaussianLaw (fun w ↦ (Z n w,D n w)) (μ n))
    (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n)
    (hVarPos : ∀ n, 0 < variance (Z n) (μ n))
    (hVarGrow : Tendsto (fun n ↦ variance (Z n) (μ n)) atTop atTop)
    (hScale : Tendsto (fun n ↦ u n/√(variance (Z n) (μ n))) atTop (𝓝 1))
    (A : ℝ) (hBaseMean : ∀ᶠ n in atTop, |∫ w, Z n w ∂μ n|≤A)
    (hBaseCov : ∀ i, ∃ R : ℝ, ∀ᶠ n in atTop,
      |covariance (Z n) (fun w ↦ D n w i) (μ n)|≤R)
    (W : H →ₗ[ℝ] (Ω' → ℝ)) (hmW : ∀ x, Measurable (W x))
    (hW : ∀ x, HasLaw (W x) (gaussianReal 0 (isoVar 1 x)) ν)
    {k : ℝ≥0} (hk : 0 < k) (f : Fin N → H) (hf : Function.Injective f)
    (hMean : ∀ i, Tendsto (fun n ↦ ∫ w, D n w i ∂μ n) atTop
      (𝓝 (∫ w, isoScore W k (f i-f j) w ∂ν)))
    (hCov : ∀ i t, Tendsto (fun n ↦ covariance (fun w ↦ D n w i) (fun w ↦ D n w t) (μ n))
      atTop (𝓝 (covariance (isoScore W k (f i-f j)) (isoScore W k (f t-f j)) ν))) :
    Tendsto (fun n ↦ u n * winnerFaceWeight (μ n) (Z n) (D n)
      (WithLp.ofLp ⁻¹' winnerDifferenceFace j))
      atTop (𝓝 (φ 0 * (ν.map (fun w i ↦ isoScore W k (f i-f j) w)).real (winnerDifferenceFace j))) := by
  let E := EuclideanSpace ℝ (Fin N)
  let a n := ∫ w, Z n w ∂μ n
  let v (n : ℕ) := (variance (Z n) (μ n)).toNNReal
  have hv (n : ℕ) : (v n:ℝ)=variance (Z n) (μ n) := Real.coe_toNNReal _ (hVarPos n).le
  have hZg (n : ℕ) : HasGaussianLaw (Z n) (μ n) :=
    (hZD n).map_fun (ContinuousLinearMap.fst ℝ ℝ E)
  have hZlp n := (hZg n).memLp_two
  have hDlp n (i : Fin N) : MemLp (fun w ↦ D n w i) 2 (μ n) :=
    ((hZD n).map_fun ((EuclideanSpace.proj i).comp (ContinuousLinearMap.snd ℝ ℝ E))).memLp_two
  have hYLp (i : Fin N) : MemLp (isoScore W k (f i-f j)) 2 ν :=
    (isoScore_hasLaw ν W hW k (f i-f j)).hasGaussianLaw.memLp_two
  choose c hc using fun n ↦ finite_euclid_regression_vector (μ n) (Z n) (D n)
    (hZlp n) (hDlp n) (hVarPos n).ne'
  have hZlaw (n : ℕ) : HasLaw (Z n) (gaussianReal (a n) (v n)) (μ n) :=
    ⟨(hmZ n).aemeasurable,(hZg n).map_eq_gaussianReal⟩
  have hScale' : Tendsto (fun n ↦ u n/√(v n:ℝ)) atTop (𝓝 1) := by simpa only [hv] using hScale
  have hOffset (x : ℝ) (_hx : x ∈ Ioi (0:ℝ)) :
      Tendsto (fun n ↦ (x-a n)/√(v n:ℝ)) atTop (𝓝 0) := by
    have hDiv : Tendsto (fun n ↦ √(v n:ℝ)) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp (by simpa only [hv] using hVarGrow)
    have hInv := tendsto_inv_atTop_zero.comp hDiv
    refine squeeze_zero_norm' ?_ (by simpa using hInv.const_mul (|x|+A))
    
    filter_upwards [hBaseMean] with n hn
    rw [Real.norm_eq_abs,div_eq_mul_inv,abs_mul,abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
    exact mul_le_mul_of_nonneg_right ((abs_sub _ _).trans (by dsimp [a]; linarith)) (by positivity)
  have hBaseCov' (L : StrongDual ℝ E) : ∃ R : ℝ, ∀ᶠ n in atTop, |covariance (Z n) (L ∘ D n) (μ n)|≤R := by
    choose R hR using hBaseCov
    refine ⟨∑ i, |L (EuclideanSpace.basisFun (Fin N) ℝ i)| * R i, ?_⟩
    filter_upwards [eventually_all.mpr hR] with n hn
    rw [finite_euclid_covariance_dual (μ n) (Z n) (D n) (hZlp n) (hDlp n) L]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hn i) (abs_nonneg _)
  have hP (L : E) := finite_coordinate_moments_imply_projected μ ν
    (fun n i w ↦ D n w i) (fun i ↦ isoScore W k (f i-f j))
    hDlp hYLp hMean hCov (fun i ↦ L i)
  have hInn (L y : E) : ⟪L,y⟫ = ∑ i, L i*y i := by
    dsimp [E]
    rw [PiLp.inner_apply]
    simp [Real.inner_apply, mul_comm]
  refine finiteGaussianWinner_coordinate_tendsto j μ ν Z D c hmZ hmD hZD hc a u v
    (fun n ↦ by exact_mod_cast (show 0<(v n:ℝ) by rw [hv]; exact hVarPos n))
    hZlaw hu hScale' hOffset W hmW hW hk f hf hVarGrow A hBaseMean hBaseCov' ?_ ?_
  · intro L
    simp_rw [hInn]
    exact (hP L).1
  · intro L
    simp_rw [hInn]
    exact (hP L).2

theorem finite_winner_limit_of_entrywise_eventually
    {Ω Ω' H : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {N : ℕ} (j : Fin N) (μ : ℕ → Measure Ω) (ν : Measure Ω')
    [∀ n, IsProbabilityMeasure (μ n)] [IsProbabilityMeasure ν]
    (Z : ℕ → Ω → ℝ) (D : ℕ → Ω → EuclideanSpace ℝ (Fin N))
    (hmZ : ∀ n, Measurable (Z n)) (hmD : ∀ n, Measurable (D n))
    (hZD : ∀ n, HasGaussianLaw (fun w ↦ (Z n w,D n w)) (μ n))
    (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n)
    (hVarPos : ∀ᶠ n in atTop, 0 < variance (Z n) (μ n))
    (hVarGrow : Tendsto (fun n ↦ variance (Z n) (μ n)) atTop atTop)
    (hScale : Tendsto (fun n ↦ u n/√(variance (Z n) (μ n))) atTop (𝓝 1))
    (A : ℝ) (hBaseMean : ∀ᶠ n in atTop, |∫ w, Z n w ∂μ n|≤A)
    (hBaseCov : ∀ i, ∃ R : ℝ, ∀ᶠ n in atTop,
      |covariance (Z n) (fun w ↦ D n w i) (μ n)|≤R)
    (W : H →ₗ[ℝ] (Ω' → ℝ)) (hmW : ∀ x, Measurable (W x))
    (hW : ∀ x, HasLaw (W x) (gaussianReal 0 (isoVar 1 x)) ν)
    {k : ℝ≥0} (hk : 0 < k) (f : Fin N → H) (hf : Function.Injective f)
    (hMean : ∀ i, Tendsto (fun n ↦ ∫ w, D n w i ∂μ n) atTop
      (𝓝 (∫ w, isoScore W k (f i-f j) w ∂ν)))
    (hCov : ∀ i t, Tendsto (fun n ↦ covariance (fun w ↦ D n w i) (fun w ↦ D n w t) (μ n))
      atTop (𝓝 (covariance (isoScore W k (f i-f j)) (isoScore W k (f t-f j)) ν))) :
    Tendsto (fun n ↦ u n * winnerFaceWeight (μ n) (Z n) (D n)
      (WithLp.ofLp ⁻¹' winnerDifferenceFace j))
      atTop (𝓝 (φ 0 * (ν.map (fun w i ↦ isoScore W k (f i-f j) w)).real (winnerDifferenceFace j))) := by

  obtain ⟨t,ht⟩ := Filter.eventually_atTop.mp hVarPos
  let g (n : ℕ) := n+t
  have hg : Tendsto g atTop atTop := (tendsto_add_atTop_iff_nat t).2 tendsto_id
  letI : ∀ n, IsProbabilityMeasure ((μ ∘ g) n) := fun n ↦ inferInstanceAs (IsProbabilityMeasure (μ (g n)))
  apply (tendsto_add_atTop_iff_nat t).1
  exact finite_winner_limit_of_entrywise j (μ ∘ g) ν (Z ∘ g) (D ∘ g)
    (fun n ↦ hmZ (g n)) (fun n ↦ hmD (g n)) (fun n ↦ hZD (g n))
    (u ∘ g) (fun n ↦ hu (g n)) (fun n ↦ ht (g n) (by dsimp [g]; omega))
    (hVarGrow.comp hg) (hScale.comp hg) A (hg.eventually hBaseMean)
    (fun i ↦ let ⟨R,hR⟩ := hBaseCov i; ⟨R,hg.eventually hR⟩)
    W hmW hW hk f hf (fun i ↦ (hMean i).comp hg) (fun i j ↦ (hCov i j).comp hg)

end CubeSqrtProbability
#print axioms CubeSqrtProbability.finite_winner_limit_of_entrywise

#print axioms CubeSqrtProbability.finite_winner_limit_of_entrywise_eventually
