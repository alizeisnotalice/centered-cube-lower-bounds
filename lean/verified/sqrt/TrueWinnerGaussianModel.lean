import GaussianFacetProjection
import GaussianFacetCoordinateMoments
import TrueTiltBaseline

open MeasureTheory ProbabilityTheory Filter WithLp
open scoped BigOperators NNReal
namespace CubeSqrtProbability

section
variable {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω)
variable {k : ℕ} (j : Fin k) (G : Ω → Fin k → ℝ)

noncomputable def trueWinnerFacetMean (i : WinnerFacet j) : ℝ :=
  ∫ w, winnerFacetScore j (G w) i ∂Q

noncomputable def trueWinnerFacetMatrix : Matrix (WinnerFacet j) (WinnerFacet j) ℝ :=
  rawSecondMoment (Q.map (fun w i ↦ winnerFacetScore j (G w) i-
    trueWinnerFacetMean Q j G i))

noncomputable def trueWinnerGaussian (n : ℕ) : Measure (WinnerFacet j → ℝ) :=
  sumLaw (centeredGaussianCompanion (trueWinnerFacetMatrix Q j G)) n

instance trueWinnerGaussian_prob (n : ℕ) : IsProbabilityMeasure (trueWinnerGaussian Q j G n) := by
  unfold trueWinnerGaussian
  infer_instance

noncomputable def trueWinnerGaussianShift (n : ℕ) (x : WinnerFacet j → ℝ) :
    WinnerFacet j → ℝ := fun i ↦ (n:ℝ)*trueWinnerFacetMean Q j G i+x i

noncomputable def trueWinnerGaussianAnchor (n : ℕ) (h : ℝ) (x : WinnerFacet j → ℝ) : ℝ :=
  trueWinnerGaussianShift Q j G n x (.inl true)-h

noncomputable def trueWinnerGaussianRelative (n : ℕ) (x : WinnerFacet j → ℝ) :
    EuclideanSpace ℝ (Fin k) :=
  toLp 2 (facetRelative j (trueWinnerGaussianShift Q j G n x))

theorem trueWinnerFacetMatrix_cov (hG : Measurable G) (i t : WinnerFacet j) :
    trueWinnerFacetMatrix Q j G i t =
    covariance (fun w ↦ winnerFacetScore j (G w) i) (fun w ↦ winnerFacetScore j (G w) t) Q :=
  centered_facet_raw_matrix_covariance Q _ ((measurable_winnerFacetScore j).comp hG) i t

theorem trueWinnerFacetMatrix_psd [IsProbabilityMeasure Q] (hG : Measurable G)
    {B : ℝ} (hB : 0≤B) (hb : ∀ w i, |winnerFacetScore j (G w) i|≤B) :
    (trueWinnerFacetMatrix Q j G).PosSemidef := by
  let F (w : Ω) := winnerFacetScore j (G w)
  let μ := Q.map (fun w i ↦ F w i-trueWinnerFacetMean Q j G i)
  haveI : IsProbabilityMeasure μ := by dsimp [μ]; infer_instance
  obtain ⟨_,hμ,_⟩ := centered_facet_coordinate_law Q F ((measurable_winnerFacetScore j).comp hG) B hB hb
  obtain ⟨h3,_⟩ := integrable_third_norm_of_bound μ (2*B) (by positivity) hμ
  apply posSemidef_rawSecondMoment μ
  intro i t
  let r : Fin 2 → WinnerFacet j := ![i,t]
  simpa [Fin.prod_univ_two,r] using integrable_coordinate_monomial_of_third_norm μ h3
    (show (2:ℕ) ≤ 3 by decide) r

theorem trueWinnerGaussian_joint (n : ℕ) (h : ℝ) :
    HasGaussianLaw (fun w ↦ (trueWinnerGaussianAnchor Q j G n h w,
      trueWinnerGaussianRelative Q j G n w)) (trueWinnerGaussian Q j G n) :=
  winnerFacet_shifted_sum_hasGaussianLaw j (trueWinnerFacetMatrix Q j G) n
    (fun i ↦ (n:ℝ)*trueWinnerFacetMean Q j G i) h

theorem trueWinnerGaussianShift_measurable (n : ℕ) :
    Measurable (trueWinnerGaussianShift Q j G n) :=
  measurable_const.add measurable_id

theorem trueWinnerGaussian_relative_of_ne (n : ℕ) (i : Fin k) (hi : i ≠ j) (w : WinnerFacet j → ℝ) :
    trueWinnerGaussianRelative Q j G n w i =
    (n:ℝ)*trueWinnerFacetMean Q j G (.inr ⟨i,hi⟩)+ w (.inr ⟨i,hi⟩) := by
  simp [trueWinnerGaussianRelative,facetRelative,hi,trueWinnerGaussianShift]

theorem trueWinnerGaussian_relative_self (n : ℕ) (w : WinnerFacet j → ℝ) :
    trueWinnerGaussianRelative Q j G n w j = 0 := by
  simp [trueWinnerGaussianRelative,facetRelative]

theorem trueWinnerGaussian_anchor_fun (n : ℕ) (h : ℝ) :
    trueWinnerGaussianAnchor Q j G n h = fun x ↦
      ((n:ℝ)*trueWinnerFacetMean Q j G (.inl true)-h)+x (.inl true) := by
  funext x
  unfold trueWinnerGaussianAnchor trueWinnerGaussianShift
  ring

theorem trueWinnerGaussian_anchor_mean (n : ℕ) (h : ℝ)
    (hS : (trueWinnerFacetMatrix Q j G).PosSemidef) :
    (∫ w, trueWinnerGaussianAnchor Q j G n h w ∂trueWinnerGaussian Q j G n) =
      (n:ℝ)*(∫ w, G w j ∂Q)-h := by
  unfold trueWinnerGaussian
  simpa only [trueWinnerGaussianAnchor,trueWinnerGaussianShift,trueWinnerFacetMean,
    winnerFacetScore,add_sub_right_comm] using gaussian_companion_affine_coord_mean
      (trueWinnerFacetMatrix Q j G) hS n (.inl true) ((n:ℝ)*(∫ w, G w j ∂Q)-h)

theorem trueWinnerGaussian_anchor_variance (n : ℕ) (h : ℝ)
    (hG : Measurable G) (hS : (trueWinnerFacetMatrix Q j G).PosSemidef) :
    variance (trueWinnerGaussianAnchor Q j G n h) (trueWinnerGaussian Q j G n) =
      (n:ℝ)*covariance (fun w ↦ G w j) (fun w ↦ G w j) Q := by
  have hm : Measurable (trueWinnerGaussianAnchor Q j G n h) :=
    ((measurable_pi_apply _).comp (trueWinnerGaussianShift_measurable Q j G n)).sub_const _
  rw [← covariance_self hm.aemeasurable]
  unfold trueWinnerGaussian
  have hC := gaussian_companion_affine_coord_cov (trueWinnerFacetMatrix Q j G) hS n
    (.inl true) (.inl true) ((n:ℝ)*trueWinnerFacetMean Q j G (.inl true)-h)
    ((n:ℝ)*trueWinnerFacetMean Q j G (.inl true)-h)
  rw [trueWinnerFacetMatrix_cov Q j G hG] at hC
  rw [trueWinnerGaussian_anchor_fun Q j G n h]
  exact hC

theorem trueWinnerGaussian_relative_mean (n : ℕ) (i : Fin k) (hi : i ≠ j)
    (hS : (trueWinnerFacetMatrix Q j G).PosSemidef) :
    (∫ w, trueWinnerGaussianRelative Q j G n w i ∂trueWinnerGaussian Q j G n) =
      (n:ℝ)*(∫ w, G w i-G w j ∂Q) := by
  unfold trueWinnerGaussian
  simp_rw [trueWinnerGaussian_relative_of_ne Q j G n i hi]
  exact gaussian_companion_affine_coord_mean (trueWinnerFacetMatrix Q j G) hS n
    (.inr ⟨i,hi⟩) ((n:ℝ)*trueWinnerFacetMean Q j G (.inr ⟨i,hi⟩))

theorem trueWinnerGaussian_relative_covariance (n : ℕ) (i t : Fin k) (hi : i ≠ j) (ht : t ≠ j)
    (hG : Measurable G) (hS : (trueWinnerFacetMatrix Q j G).PosSemidef) :
    covariance (fun w ↦ trueWinnerGaussianRelative Q j G n w i)
      (fun w ↦ trueWinnerGaussianRelative Q j G n w t) (trueWinnerGaussian Q j G n) =
        (n:ℝ)*covariance (fun w ↦ G w i-G w j) (fun w ↦ G w t-G w j) Q := by
  unfold trueWinnerGaussian
  simp_rw [trueWinnerGaussian_relative_of_ne Q j G n i hi,trueWinnerGaussian_relative_of_ne Q j G n t ht]
  rw [gaussian_companion_affine_coord_cov (trueWinnerFacetMatrix Q j G) hS n,
    trueWinnerFacetMatrix_cov Q j G hG]
  rfl

theorem trueWinnerGaussian_anchor_relative_covariance (n : ℕ) (h : ℝ) (i : Fin k) (hi : i ≠ j)
    (hG : Measurable G) (hS : (trueWinnerFacetMatrix Q j G).PosSemidef) :
    covariance (trueWinnerGaussianAnchor Q j G n h)
      (fun w ↦ trueWinnerGaussianRelative Q j G n w i) (trueWinnerGaussian Q j G n) =
        (n:ℝ)*covariance (fun w ↦ G w j) (fun w ↦ G w i-G w j) Q := by
  unfold trueWinnerGaussian
  rw [trueWinnerGaussian_anchor_fun Q j G n h]
  simp_rw [trueWinnerGaussian_relative_of_ne Q j G n i hi]
  rw [gaussian_companion_affine_coord_cov (trueWinnerFacetMatrix Q j G) hS n,
    trueWinnerFacetMatrix_cov Q j G hG]
  rfl

end
end CubeSqrtProbability
#print axioms CubeSqrtProbability.trueWinnerFacetMatrix_psd
#print axioms CubeSqrtProbability.trueWinnerGaussian_joint
#print axioms CubeSqrtProbability.trueWinnerGaussian_anchor_mean
#print axioms CubeSqrtProbability.trueWinnerGaussian_anchor_variance
#print axioms CubeSqrtProbability.trueWinnerGaussian_relative_mean
#print axioms CubeSqrtProbability.trueWinnerGaussian_relative_covariance
#print axioms CubeSqrtProbability.trueWinnerGaussian_anchor_relative_covariance
