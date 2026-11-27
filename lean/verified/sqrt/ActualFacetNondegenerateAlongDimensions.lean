import TrueWinnerMomentLimitAlongDimensions
import TrueWinnerWeightAsymptotic

open MeasureTheory ProbabilityTheory Filter WithLp
open scoped NNReal Topology
namespace CubeSqrtProbability

private theorem finite_pos_common_dimensions {I : Type*} [Fintype I] (c : I → ℝ)
    (hc : ∀ i, 0<c i) : ∃ b : ℝ, 0<b ∧ ∀ i, b ≤ c i := by
  classical
  have H (s : Finset I) : ∃ b : ℝ, 0<b ∧ ∀ i ∈ s, b ≤ c i := by
    induction s using Finset.induction_on with
    | empty => exact ⟨1,by norm_num,by simp⟩
    | insert i s _ ih =>
      obtain ⟨b,hb,h⟩ := ih
      refine ⟨min b (c i),lt_min hb (hc i),?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (h j hj)
  obtain ⟨b,hb,h⟩ := H Finset.univ
  exact ⟨b,hb,fun i ↦ h i (Finset.mem_univ _)⟩

/-- The finite facets all have positive total variance bounded away from zero.
The two base facets diverge and the other facets use the exact raw node
distance limits. The whole covariance matrix may remain singular. -/
theorem actual_winner_facet_nondegenerate_along_dimensions {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {N : ℕ} (P : Measure Ω) [IsProbabilityMeasure P] (j : Fin N)
    (dim : ℕ → ℕ) (hDim : Tendsto dim atTop atTop)
    (d : Fin N → ℕ → Ω → ℝ) (a v : ℕ → ℝ)
    (hm : ∀ i n, Measurable (d i n))
    (ha0 : ∀ n, 0 ≤ a n) (ha : ∀ n, a n ≤ 1/2) (hb : ∀ i n w, |d i n w| ≤ a n)
    (hZero : ∀ i n, (∫ w, d i n w ∂P)=0)
    (haLim : Tendsto a atTop (𝓝 0)) (hV : Tendsto v atTop atTop)
    (hSmall : ∀ i, Tendsto (fun n : ℕ ↦ (dim n:ℝ)*a n*rawSq P (d i n)) atTop (𝓝 0))
    (hQSq : Tendsto (fun n : ℕ ↦ ((dim n:ℝ)*rawSq P (d j n))^2/(dim n:ℝ)) atTop (𝓝 0))
    (E : ℝ) (hQ : ∀ᶠ n : ℕ in atTop, |(dim n:ℝ)*rawSq P (d j n)-v n| ≤ E)
    {k : ℝ≥0} (hk : 0 < k) (f : Fin N → H) (hf : Function.Injective f)
    (hDist : ∀ i t, Tendsto (fun n : ℕ ↦ (dim n:ℝ)*rawSq P (fun w ↦ d i n w-d t n w)) atTop
      (𝓝 ((k:ℝ)*‖f i-f t‖^2))) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop, ∀ i : WinnerFacet j,
      c ≤ ((dim n • (trueWinnerFacetMatrix (winnerTilt P (d j n)) j
        (trueLogScores (fun i ↦ d i n)) i i).toNNReal : ℝ≥0):ℝ) := by
  let Q n := winnerTilt P (d j n)
  let G n := trueLogScores (fun i ↦ d i n)
  let S n := trueWinnerFacetMatrix (Q n) j (G n)
  have hmG n : Measurable (G n) := Measurable.of_eval fun i ↦
    Real.measurable_log.comp (measurable_const.add (hm i n))
  have hS (n : ℕ) (i : WinnerFacet j) : 0 ≤ S n i i := by
    rw [show S n i i =
      covariance (fun w ↦ winnerFacetScore j (G n w) i) (fun w ↦ winnerFacetScore j (G n w) i) (Q n)
      from trueWinnerFacetMatrix_cov (Q n) j (G n) (hmG n) i i]
    have hmS : Measurable (fun w ↦ winnerFacetScore j (G n w) i) :=
      (measurable_pi_apply i).comp ((measurable_winnerFacetScore j).comp (hmG n))
    rw [covariance_self (μ := Q n) hmS.aemeasurable]
    exact variance_nonneg _ _
  have hSconv (n : ℕ) (i : WinnerFacet j) : ((dim n • (S n i i).toNNReal : ℝ≥0):ℝ) =
    (dim n:ℝ)*S n i i := by
      simp [nsmul_eq_mul,Real.coe_toNNReal _ (hS n i)]
  have hEach (i : WinnerFacet j) : ∃ c : ℝ, 0<c ∧
      ∀ᶠ n : ℕ in atTop, c ≤ (dim n:ℝ)*S n i i := by
    rcases i with b | i
    · have hVcorr := true_winner_base_variance_difference_tendsto_along_dimensions P dim hDim (d j) a (hm j) ha0 ha
        (hb j) (hZero j) (hSmall j) hQSq
      refine ⟨1,by norm_num,?_⟩
      filter_upwards [eventually_abs_le_of_tendsto_real hVcorr,hQ,hV.eventually_gt_atTop (E+2)] with n hc hq hv
      have e : S n (.inl b) (.inl b) = covariance (winnerBaseLog (d j n)) (winnerBaseLog (d j n)) (Q n) := by
        rw [show S n (.inl b) (.inl b) = covariance (fun w ↦ winnerFacetScore j (G n w) (.inl b))
          (fun w ↦ winnerFacetScore j (G n w) (.inl b)) (Q n)
          from trueWinnerFacetMatrix_cov (Q n) j (G n) (hmG n) _ _]
        cases b <;> simp [G,trueLogScores,winnerFacetScore,winnerBaseLog,covariance_fun_neg_left,covariance_fun_neg_right] <;> rfl
      rw [e]
      have h1 := (abs_le.mp hc).1
      have h2 := (abs_le.mp hq).1
      simp only [abs_zero,zero_add] at h1
      dsimp [Q]
      linarith
    · let M := (k:ℝ)*‖f i.val-f j‖^2
      have hp : 0<M := by
        have hk' : 0<(k:ℝ) := by exact_mod_cast hk
        have ne : f i.val-f j ≠ 0 := sub_ne_zero.mpr fun h ↦ i.property (hf h)
        dsimp [M]
        positivity
      have hSmallPair : Tendsto (fun n : ℕ ↦ (dim n:ℝ)*a n*
          (rawSq P (d j n)+rawSq P (d i.val n))) atTop (𝓝 0) := by
        simpa [mul_add] using (hSmall j).add (hSmall i.val)
      have hv0 : Tendsto (fun n : ℕ ↦ (dim n:ℝ)*rawSq P (fun w ↦ d i.val n w-d i.val n w))
          atTop (𝓝 0) := by simp [rawSq]
      have h := true_winner_tilted_covariance_of_distances_along_dimensions P dim hDim (d j) (d i.val) (d i.val) a
        (hm j) (hm i.val) (hm i.val) ha0 ha (hb j) (hb i.val) (hb i.val)
        (hZero j) (hZero i.val) (hZero i.val) haLim (hDist i.val j) (hDist i.val j) hv0
        hSmallPair hSmallPair
      have h' : Tendsto (fun n : ℕ ↦ (dim n:ℝ)*S n (.inr i) (.inr i)) atTop (𝓝 M) := by
        have he : M+M-0=2*M := by ring
        apply (show Tendsto _ atTop (𝓝 M) by
          have e : ((k:ℝ)*‖f i.val-f j‖^2+(k:ℝ)*‖f i.val-f j‖^2-0)/2=M := by dsimp [M]; ring
          rwa [e] at h).congr
        intro n
        rw [show S n (.inr i) (.inr i) =
          covariance (fun w ↦ winnerFacetScore j (G n w) (.inr i))
            (fun w ↦ winnerFacetScore j (G n w) (.inr i)) (Q n)
          from trueWinnerFacetMatrix_cov (Q n) j (G n) (hmG n) _ _]
        rfl
      refine ⟨M/2,by positivity,?_⟩
      have hh := Metric.tendsto_nhds.mp h' (M/2) (by positivity)
      filter_upwards [hh] with n hn
      rw [Real.dist_eq] at hn
      linarith [(abs_lt.mp hn).1]
  choose c hc hcx using hEach
  obtain ⟨b,hb,hbc⟩ := finite_pos_common_dimensions c hc
  refine ⟨b,hb,?_⟩
  filter_upwards [eventually_all.mpr hcx] with n hn i
  rw [hSconv]
  exact (hbc i).trans (hn i)

end CubeSqrtProbability
#print axioms CubeSqrtProbability.actual_winner_facet_nondegenerate_along_dimensions
