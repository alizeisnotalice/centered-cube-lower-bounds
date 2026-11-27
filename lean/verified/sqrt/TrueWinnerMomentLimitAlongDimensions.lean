import TrueTiltAlongDimensions
import TrueWinnerGaussianModel
import FiniteWinnerEntrywise
import WinnerScalarNormalization
import RawWinnerReanchor

open MeasureTheory ProbabilityTheory Filter WithLp CubeBrownian
open scoped NNReal ENNReal Topology ProbabilityTheory RealInnerProductSpace
namespace CubeSqrtProbability

/-- Fixed safe-window Gaussian half of the paperwinner theorem, reduced
to the actual untilted local distance and nuisance base estimates. -/
theorem true_esscher_gaussian_winner_limit_along_dimensions
    {Ω Ω' H : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {N : ℕ} (P : Measure Ω) [IsProbabilityMeasure P] (j : Fin N)
    (dim : ℕ → ℕ) (hDim : Tendsto dim atTop atTop)
    (d : Fin N → ℕ → Ω → ℝ) (a v h : ℕ → ℝ)
    (hDmeas : ∀ i n, Measurable (d i n))
    (ha0 : ∀ n, 0≤a n) (ha : ∀ n, a n≤1/2) (hamp : ∀ i n w, |d i n w|≤a n)
    (hZero : ∀ i n, (∫ w, d i n w ∂P)=0)
    (haLim : Tendsto a atTop (𝓝 0)) (hV : Tendsto v atTop atTop)
    (hSmall : ∀ i, Tendsto (fun n : ℕ ↦ (dim n:ℝ)*a n*rawSq P (d i n)) atTop (𝓝 0))
    (hSqZero : Tendsto (fun n ↦ rawSq P (d j n)) atTop (𝓝 0))
    (hQSq : Tendsto (fun n : ℕ ↦ ((dim n:ℝ)*rawSq P (d j n))^2/(dim n:ℝ)) atTop (𝓝 0))
    (E : ℝ) (hQ : ∀ᶠ n : ℕ in atTop, ∀ i, |(dim n:ℝ)*rawSq P (d i n)-v n|≤E)
    (A : ℝ) (hh : ∀ᶠ n : ℕ in atTop, |v n/2-h n|≤A)
    (ν : Measure Ω') [IsProbabilityMeasure ν]
    (W : H →ₗ[ℝ] (Ω' → ℝ)) (hmW : ∀ x, Measurable (W x))
    (hW : ∀ x, HasLaw (W x) (gaussianReal 0 (isoVar 1 x)) ν)
    {k : ℝ≥0} (hk : 0 < k) (f : Fin N → H) (hf : Function.Injective f)
    (hDist : ∀ i t, Tendsto (fun n : ℕ ↦ (dim n:ℝ)*rawSq P (fun w ↦ d i n w-d t n w)) atTop
      (𝓝 ((k:ℝ)*‖f i-f t‖^2))) :
    let Q (n : ℕ) := winnerTilt P (d j n)
    let G (n : ℕ) (w : Ω) (i : Fin N) := Real.log (1+d i n w)
    Tendsto (fun n ↦ √(v n)*winnerFaceWeight (trueWinnerGaussian (Q n) j (G n) (dim n))
      (trueWinnerGaussianAnchor (Q n) j (G n) (dim n) (h n))
      (trueWinnerGaussianRelative (Q n) j (G n) (dim n))
      (WithLp.ofLp ⁻¹' winnerDifferenceFace j))
      atTop (𝓝 (φ 0 * (ν.map (fun w i ↦ isoScore W k (f i-f j) w)).real (winnerDifferenceFace j))) := by
  let Q (n : ℕ) := winnerTilt P (d j n)
  let G (n : ℕ) (w : Ω) (i : Fin N) := Real.log (1+d i n w)
  let q (n : ℕ) (i : Fin N) := (dim n:ℝ)*rawSq P (d i n)
  let dist (n : ℕ) (i t : Fin N) := (dim n:ℝ)*rawSq P (fun w ↦ d i n w-d t n w)
  let μ n := trueWinnerGaussian (Q n) j (G n) (dim n)
  let Z n := trueWinnerGaussianAnchor (Q n) j (G n) (dim n) (h n)
  let D n := trueWinnerGaussianRelative (Q n) j (G n) (dim n)
  let L (i t : Fin N) := (k:ℝ)*‖f i-f t‖^2
  have hmG n : Measurable (G n) := Measurable.of_eval fun i ↦
    Real.measurable_log.comp (measurable_const.add (hDmeas i n))
  haveI hProb (n : ℕ) : IsProbabilityMeasure (Q n) := by
    apply isProbabilityMeasure_tilted
    simp_rw [show ∀ w, Real.exp (Real.log (1+d j n w))=1+d j n w from
      fun w ↦ exp_logPerturbation_eq (ha n) (hamp j n w)]
    exact (integrable_const 1).add (integrable_of_uniform_abs P (hDmeas j n) (hamp j n))
  have hPSD n : (trueWinnerFacetMatrix (Q n) j (G n)).PosSemidef :=
    trueWinnerFacetMatrix_psd (Q n) j (G n) (hmG n) (show 0≤4*a n by exact mul_nonneg (by norm_num) (ha0 n))
      (log_perturbation_winnerFacetScore_bound j (fun i ↦ d i n) (ha n) (fun i ↦ hamp i n))
  have hShift n : Measurable (trueWinnerGaussianShift (Q n) j (G n) (dim n)) :=
    trueWinnerGaussianShift_measurable (Q n) j (G n) (dim n)
  have hmZ n : Measurable (Z n) :=
    ((measurable_pi_apply _).comp (hShift n)).sub_const _
  have hmD n : Measurable (D n) :=
    (WithLp.measurable_toLp 2 (Fin N → ℝ)).comp ((measurable_facetRelative j).comp (hShift n))
  have hJV n : HasGaussianLaw (fun w ↦ (Z n w,D n w)) (μ n) :=
    trueWinnerGaussian_joint (Q n) j (G n) (dim n) (h n)
  have hMeanDiff := true_winner_base_mean_difference_tendsto_along_dimensions P dim (d j) a (hDmeas j) ha
    (hamp j) (hZero j) (hSmall j)
  have hVarDiff := true_winner_base_variance_difference_tendsto_along_dimensions P dim hDim (d j) a (hDmeas j) ha0 ha
    (hamp j) (hZero j) (hSmall j) hQSq
  have hAnMean n : (∫ w, Z n w ∂μ n) = (dim n:ℝ)*winnerBaseMean P (d j n)-h n :=
    trueWinnerGaussian_anchor_mean (Q n) j (G n) (dim n) (h n) (hPSD n)
  have hAnVar n : variance (Z n) (μ n) =
      (dim n:ℝ)*covariance (winnerBaseLog (d j n)) (winnerBaseLog (d j n)) (Q n) :=
    trueWinnerGaussian_anchor_variance (Q n) j (G n) (dim n) (h n) (hmG n) (hPSD n)
  have hVarBound : ∀ᶠ n : ℕ in atTop, |variance (Z n) (μ n)-v n|≤1+E := by
    filter_upwards [eventually_abs_le_of_tendsto_real hVarDiff,hQ] with n hd hq
    have e := hq j
    rw [hAnVar]
    rw [show (dim n:ℝ)*covariance (winnerBaseLog (d j n)) (winnerBaseLog (d j n)) (Q n)-v n =
      ((dim n:ℝ)*covariance (winnerBaseLog (d j n)) (winnerBaseLog (d j n)) (Q n)-q n j)+(q n j-v n) by ring]
    exact (abs_add_le _ _).trans (by simpa [q,Q] using add_le_add hd e)
  obtain ⟨hGrow,hScale⟩ := winner_anchor_normalization v (fun n ↦ variance (Z n) (μ n)) hV hVarBound
  have hMeanBound : ∀ᶠ n : ℕ in atTop, |∫ w, Z n w ∂μ n|≤1+E/2+A := by
    filter_upwards [eventually_abs_le_of_tendsto_real hMeanDiff,hQ,hh] with n hd hq hh'
    have e : |(q n j-v n)/2|≤E/2 := by rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]; exact div_le_div_of_nonneg_right (hq j) (by norm_num)
    rw [hAnMean,show (dim n:ℝ)*winnerBaseMean P (d j n)-h n =
      ((dim n:ℝ)*winnerBaseMean P (d j n)-q n j/2)+(q n j-v n)/2+(v n/2-h n) by ring]
    exact (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans
      (by simpa [q] using add_le_add hd e)) hh')
  have hSmallPair (i t : Fin N) : Tendsto (fun n : ℕ ↦ (dim n:ℝ)*a n*
      (rawSq P (d i n)+rawSq P (d t n))) atTop (𝓝 0) := by
    simpa [mul_add] using (hSmall i).add (hSmall t)
  have hIncMean (i : Fin N) : Tendsto (fun n : ℕ ↦ (dim n:ℝ)*tiltedIncMean P (d j n) (d i n))
      atTop (𝓝 (-(L i j)/2)) :=
    true_winner_tilted_mean_tendsto_along_dimensions P dim (d j) (d i) a (hDmeas j) (hDmeas i) ha
      (hamp j) (hamp i) (hZero j) (hZero i) (hDist i j) (hSmallPair j i)
  have hBaseZero : Tendsto (fun n ↦ winnerBaseMean P (d j n)) atTop (𝓝 0) := by
    refine squeeze_zero_norm' (Eventually.of_forall fun n ↦ ?_) (by simpa using hSqZero.const_mul (5/2))
    rw [Real.norm_eq_abs]
    exact true_winner_base_mean_abs_le P (d j n) (hDmeas j n) (ha n) (hamp j n) (hZero j n)
  have hCrossRaw (i : Fin N) : ∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
      |(dim n:ℝ)*∫ w, d j n w*(d i n w-d j n w) ∂P|≤C := by
    refine ⟨(2*E+(|L i j|+1))/2,?_⟩
    filter_upwards [hQ,eventually_abs_le_of_tendsto_real (hDist i j)] with n hn hd
    have e : (dim n:ℝ)*(∫ w, d j n w*(d i n w-d j n w) ∂P) =
        ((q n i-v n)-(q n j-v n)-dist n i j)/2 := by
      dsimp [q,dist]
      have e := raw_reanchor_variance_exact P (d j n) (d i n) (hDmeas j n) (hDmeas i n)
        (ha0 n) (hamp j n) (hamp i n)
      linear_combination -(dim n:ℝ)/2 * e
    rw [e,abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
    exact div_le_div_of_nonneg_right
      ((abs_sub _ _).trans (add_le_add ((abs_sub _ _).trans (by linarith [hn i,hn j])) hd)) (by norm_num)
  have hCross (i : Fin N) : ∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
      |covariance (Z n) (fun w ↦ D n w i) (μ n)|≤C := by
    by_cases hi : i=j
    · subst i
      exact ⟨0,Eventually.of_forall fun n ↦ by simp [D,trueWinnerGaussian_relative_self,covariance_const_right]⟩
    obtain ⟨C,hC⟩ := hCrossRaw i
    have hsmall : Tendsto (fun n : ℕ ↦ (dim n:ℝ)*a n*(rawSq P (d j n)+
        rawSq P (fun w ↦ d i n w-d j n w))) atTop (𝓝 0) := by
      have e := haLim.mul (hDist i j)
      simpa [mul_add,mul_comm,mul_left_comm,mul_assoc] using (hSmall j).add e
    have hdiff := true_winner_base_inc_cov_difference_tendsto_along_dimensions P dim (d j) (d i) a
      (hDmeas j) (hDmeas i) ha0 ha (hamp j) (hamp i) (hZero j) hsmall hBaseZero (hIncMean i)
    refine ⟨1+C,?_⟩
    filter_upwards [hC,eventually_abs_le_of_tendsto_real hdiff] with n hn hd
    rw [show covariance (Z n) (fun w ↦ D n w i) (μ n) =
      (dim n:ℝ)*covariance (winnerBaseLog (d j n)) (logInc (d j n) (d i n)) (Q n)
      from trueWinnerGaussian_anchor_relative_covariance (Q n) j (G n) (dim n) (h n) i hi (hmG n) (hPSD n)]
    have ea := abs_add_le
      ((dim n:ℝ)*(covariance (winnerBaseLog (d j n)) (logInc (d j n) (d i n)) (Q n)-
      ∫ w, d j n w*(d i n w-d j n w) ∂P))
      ((dim n:ℝ)*∫ w, d j n w*(d i n w-d j n w) ∂P)
    exact (by convert ea.trans (add_le_add (by simpa using hd) hn) using 2 <;> ring)
  refine finite_winner_limit_of_entrywise_eventually j μ ν Z D hmZ hmD hJV
    (fun n ↦ √(v n)) (fun _ ↦ Real.sqrt_nonneg _) (hGrow.eventually_gt_atTop 0)
    hGrow hScale (1+E/2+A) hMeanBound hCross W hmW hW hk f hf ?_ ?_
  · intro i
    have hRef := (isoScore_hasLaw ν W hW k (f i-f j)).integral_eq
    rw [integral_id_gaussianReal] at hRef
    rw [hRef]
    by_cases hi : i=j
    · subst i
      simp [D,trueWinnerGaussian_relative_self,isoVar]
    simpa only [D,μ,trueWinnerGaussian_relative_mean _ _ _ _ _ hi (hPSD _),G,Q,tiltedIncMean,logInc,L,isoVar,NNReal.coe_mul,NNReal.coe_mk] using hIncMean i
  · intro i t
    rw [isoScore_covariance ν W hW]
    by_cases hi : i=j
    · subst i
      simp [D,trueWinnerGaussian_relative_self,covariance_const_left]
    by_cases ht : t=j
    · subst t
      simp [D,trueWinnerGaussian_relative_self,covariance_const_right]
    have cv := true_winner_tilted_covariance_of_distances_along_dimensions P dim hDim (d j) (d i) (d t) a
      (hDmeas j) (hDmeas i) (hDmeas t) ha0 ha (hamp j) (hamp i) (hamp t)
      (hZero j) (hZero i) (hZero t) haLim (hDist i j) (hDist t j) (hDist i t)
      (hSmallPair j i) (hSmallPair j t)
    have hp : (L i j+L t j-L i t)/2 = (k:ℝ)*⟪f i-f j,f t-f j⟫ := by
      dsimp [L]
      have he : f i-f t=(f i-f j)-(f t-f j) := by abel
      rw [show ‖f i-f t‖^2=‖(f i-f j)-(f t-f j)‖^2 from congrArg (fun x : H ↦ ‖x‖^2) he,
        norm_sub_sq_real (f i-f j) (f t-f j)]
      ring
    rw [← hp]
    exact cv.congr (fun n ↦ (trueWinnerGaussian_relative_covariance (Q n) j (G n) (dim n) i t
      hi ht (hmG n) (hPSD n)).symm)

end CubeSqrtProbability
#print axioms CubeSqrtProbability.true_esscher_gaussian_winner_limit_along_dimensions
