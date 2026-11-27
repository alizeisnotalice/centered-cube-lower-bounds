import TrueWinnerGaussianModel
import WinnerFacetRateInputs
import FiniteWinnerMainTerm

open MeasureTheory ProbabilityTheory Filter WithLp CubeBrownian
open scoped BigOperators NNReal ENNReal Topology
namespace CubeSqrtProbability

theorem trueWinnerFacetMatrix_diag_sqrt_le {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q] {k : ℕ} (j : Fin k)
    (G : Ω → Fin k → ℝ) (hG : Measurable G)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ w i, |winnerFacetScore j (G w) i| ≤ B)
    (i : WinnerFacet j) :
    √((trueWinnerFacetMatrix Q j G i i).toNNReal:ℝ)  ≤  2*B := by
  let F (w : Ω) := winnerFacetScore j (G w)
  let μ := Q.map (fun w i ↦ F w i-trueWinnerFacetMean Q j G i)
  haveI : IsProbabilityMeasure μ := by dsimp [μ]; infer_instance
  obtain ⟨_,hμ,_⟩ := centered_facet_coordinate_law Q F ((measurable_winnerFacetScore j).comp hG) B hB hb
  have hBμ : ∀ᵐ x ∂μ, |x i| ≤ 2*B :=
    hμ.mono fun x hx ↦ by rw [← Real.norm_eq_abs]; exact (norm_le_pi_norm x i).trans hx
  have hI : Integrable (fun x : WinnerFacet j → ℝ ↦ x i^2) μ := by
    apply (integrable_const ((2*B)^2)).mono' ((measurable_pi_apply i).pow_const 2).aestronglyMeasurable
    exact hBμ.mono fun w hw ↦ by
      rw [Real.norm_eq_abs,abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) hw _
  have hS : trueWinnerFacetMatrix Q j G i i = ∫ x : WinnerFacet j → ℝ, x i^2 ∂μ := by
    unfold trueWinnerFacetMatrix rawSecondMoment
    simp [pow_two,μ,F]
  have hu : trueWinnerFacetMatrix Q j G i i  ≤  (2*B)^2 := by
    rw [hS]
    simpa using integral_mono_ae hI (integrable_const ((2*B)^2))
      (hBμ.mono fun w hw ↦ by
        change w i^2  ≤  (2*B)^2
        calc
          _ = |w i|^2 := (sq_abs _).symm
          _  ≤  _ := pow_le_pow_left₀ (abs_nonneg _) hw _)
  have h0 : 0  ≤  trueWinnerFacetMatrix Q j G i i := by rw [hS]; positivity
  rw [Real.coe_toNNReal _ h0,← Real.sqrt_sq (show 0 ≤ 2*B by positivity)]
  exact Real.sqrt_le_sqrt hu

noncomputable def trueScoreSum {Ω : Type*} {k : ℕ} {n : ℕ}
    (G : Ω → Fin k → ℝ) (w : Fin n → Ω) (i : Fin k) : ℝ :=
  ∑ c, G (w c) i

noncomputable def trueLogScores {Ω : Type*} {k : ℕ} (d : Fin k → Ω → ℝ) (w : Ω) (i : Fin k) : ℝ :=
  Real.log (1+d i w)

theorem true_facetRelative_scoreSum {Ω : Type*} {k n : ℕ} (j : Fin k)
    (G : Ω → Fin k → ℝ) (w : Fin n → Ω) :
    facetRelative j (∑ c, winnerFacetScore j (G (w c))) =
      fun i ↦ trueScoreSum G w i-trueScoreSum G w j := by
  rw [← winnerFacetScore_sum]
  funext i
  by_cases hi : i ≠ j
  · simp [facetRelative,hi,winnerFacetScore,trueScoreSum,Finset.sum_apply]
  · have e : i=j := not_ne_iff.mp hi
    subst i
    simp [facetRelative]

/-- Exact weighted error asymptotic for the manuscript's actual product
samples at fixed finitely many nodes; the eventually positive face
variances allow arbitrary rank deficiency. -/
theorem true_winner_weight_difference_tendsto
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {k : ℕ} (j : Fin k) (d : ℕ → Fin k → Ω → ℝ) (a v h : ℕ → ℝ)
    (hm : ∀ n i, Measurable (d n i))
    (ha0 : ∀ n, 0 ≤ a n) (ha : ∀ n, a n ≤ 1/2) (hb : ∀ n i w, |d n i w| ≤ a n)
    (M : ℝ) (hM : 0 ≤ M) (hvlog : ∀ᶠ n in atTop, 0 ≤ v n ∧ v n ≤ M*Real.log (n:ℝ))
    (C : ℝ) (hC : 0 ≤ C)
    (hamp : ∀ᶠ n : ℕ in atTop, 8*a n ≤ C*(√(v n)*(n:ℝ)^(-(1/2:ℝ))))
    (c : ℝ) (hc : 0<c)
    (hDiag : ∀ᶠ n in atTop, ∀ i : WinnerFacet j,
      c  ≤  ((n • (trueWinnerFacetMatrix (winnerTilt P (d n j)) j (trueLogScores (d n)) i i).toNNReal : ℝ≥0):ℝ)) :
    let G n := trueLogScores (d n)
    let Q n := winnerTilt P (d n j)
    let R (n : ℕ) := (Measure.pi fun _ : Fin n ↦ P).tilted (fun w ↦ trueScoreSum (G n) w j)
    Tendsto (fun n : ℕ ↦ √(v n)*
      (winnerFaceWeight (R n) (fun w ↦ trueScoreSum (G n) w j-h n)
        (fun w i ↦ trueScoreSum (G n) w i-trueScoreSum (G n) w j) (winnerDifferenceFace j) -
      winnerFaceWeight (trueWinnerGaussian (Q n) j (G n) n) (trueWinnerGaussianAnchor (Q n) j (G n) n (h n))
        (trueWinnerGaussianRelative (Q n) j (G n) n) (WithLp.ofLp ⁻¹' winnerDifferenceFace j)))
      atTop (𝓝 0) := by
  classical
  dsimp only
  let G n := trueLogScores (d n)
  let Q n := winnerTilt P (d n j)
  let R (n : ℕ) := (Measure.pi fun _ : Fin n ↦ P).tilted (fun w ↦ trueScoreSum (G n) w j)
  let s n (i : WinnerFacet j) := (trueWinnerFacetMatrix (Q n) j (G n) i i).toNNReal
  let third n := (2*(4*a n))^3 + stdGaussianThird*∑ i, (√(s n i:ℝ))^3
  let strip (n : ℕ) := ∑ i : WinnerFacet j, (√(2*Real.pi*((n • s n i : ℝ≥0):ℝ)))⁻¹
  obtain ⟨K,hK,hEst⟩ := exists_true_tilt_winner_weight_estimate j
  have hM0 n : Measurable (G n) := Measurable.of_eval fun i ↦
    Real.measurable_log.comp (measurable_const.add (hm n i))
  have hF n : Integrable (fun w ↦ Real.exp (G n w j)) P := by
    dsimp [G,trueLogScores]
    simp_rw [show ∀ w, Real.exp (Real.log (1+d n j w))=1+d n j w from
      fun w ↦ exp_logPerturbation_eq (ha n) (hb n j w)]
    exact (integrable_const 1).add (integrable_of_uniform_abs P (hm n j) (hb n j))
  haveI (n : ℕ) : IsProbabilityMeasure (Q n) := isProbabilityMeasure_tilted (hF n)
  have hB n : 0 ≤ 4*a n := mul_nonneg (by norm_num) (ha0 n)
  have hFacet n : ∀ w i, |winnerFacetScore j (G n w) i| ≤ 4*a n :=
    log_perturbation_winnerFacetScore_bound j (d n) (ha n) (hb n)
  let C3 := (2*C)^3+stdGaussianThird*(Fintype.card (WinnerFacet j):ℝ)*C^3
  let S0 := (Fintype.card (WinnerFacet j):ℝ)*(√(2*Real.pi*c))⁻¹
  have hStd : 0  ≤  stdGaussianThird := by unfold stdGaussianThird; positivity
  have hThird : ∀ᶠ n : ℕ in atTop, 0 ≤ third n ∧
      third n ≤ C3*(√(v n)*(n:ℝ)^(-(1/2:ℝ)))^3 := by
    filter_upwards [hamp] with n hn
    apply winner_facet_third_bound (s n) (D := C) (U := √(v n)*(n:ℝ)^(-(1/2:ℝ))) (hB n) (by linarith [ha0 n])
    intro i
    exact (trueWinnerFacetMatrix_diag_sqrt_le (Q n) j (G n) (hM0 n) (hB n) (hFacet n) i).trans
      (by linarith)
  have hStrip : ∀ᶠ n : ℕ in atTop, 0 ≤ strip n ∧ strip n ≤ S0 :=
    hDiag.mono fun n hn ↦ winner_facet_strip_bound (s n) n hc hn
  have hLim := actual_winner_weight_rate_zero v third strip M C3 S0 K hM
    (by dsimp [C3]; positivity) (by dsimp [S0]; positivity) hK hvlog hThird hStrip
  refine squeeze_zero_norm' ?_ hLim
  filter_upwards [hDiag,eventually_ge_atTop (1:ℕ)] with n hn hn1
  have hn0 : 0 < (n:ℝ) := by exact_mod_cast (show 0<n by omega)
  have hη : 0 < (n:ℝ)^(-(1/8:ℝ)) := Real.rpow_pos_of_pos hn0 _
  have hs (i : WinnerFacet j) : n • s n i ≠ 0 := by
    intro he
    have h := hn i
    change c  ≤  ((n • s n i : ℝ≥0):ℝ) at h
    rw [he,NNReal.coe_zero] at h
    linarith
  have e := hEst P (fun w ↦ G n w j) (hF n) (G n) (hM0 n) (4*a n) (hB n)
    (hFacet n) n (h n) ((n:ℝ)^(-(1/8:ℝ))) hη hs
  have hLeft (w : Fin n → Ω) : (∑ i, winnerFacetScore j (G n (w i))) (.inl true) =
      trueScoreSum (G n) w j := by simp [trueScoreSum,Finset.sum_apply,winnerFacetScore]
  simp_rw [hLeft,Function.comp_def,true_facetRelative_scoreSum] at e
  have hRight : winnerFaceWeight (trueWinnerGaussian (Q n) j (G n) n)
      (trueWinnerGaussianAnchor (Q n) j (G n) n (h n))
      (trueWinnerGaussianRelative (Q n) j (G n) n) (WithLp.ofLp ⁻¹' winnerDifferenceFace j) =
    winnerFaceWeight (trueWinnerGaussian (Q n) j (G n) n)
      (trueWinnerGaussianAnchor (Q n) j (G n) n (h n))
      (facetRelative j ∘ trueWinnerGaussianShift (Q n) j (G n) n) (facetWinnerRegion j) := rfl
  rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (Real.sqrt_nonneg _),hRight]
  exact mul_le_mul_of_nonneg_left e (Real.sqrt_nonneg _)

end CubeSqrtProbability
#print axioms CubeSqrtProbability.trueWinnerFacetMatrix_diag_sqrt_le
#print axioms CubeSqrtProbability.true_facetRelative_scoreSum
#print axioms CubeSqrtProbability.true_winner_weight_difference_tendsto
