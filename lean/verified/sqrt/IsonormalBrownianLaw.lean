import IsonormalCoupling
import BoxNodeApproximation
import Mathlib.Probability.BrownianMotion.Basic

open MeasureTheory ProbabilityTheory Finset Set Filter
open scoped NNReal ENNReal Topology ProbabilityTheory RealInnerProductSpace
namespace CubeBrownian

theorem isonormal_covariance
    {Ω H : Type*} [MeasurableSpace Ω] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (W : H →ₗ[ℝ] (Ω → ℝ))
    (hW : ∀ x, HasLaw (W x) (gaussianReal 0 (isoVar 1 x)) μ) (x y : H) :
    cov[W x,W y;μ] = ⟪x,y⟫ := by
  have hvar (z : H) : Var[W z; μ] = ‖z‖^2 := by
    have h := (hW z).variance_eq
    change Var[W z; μ] = Var[fun x : ℝ ↦ x; gaussianReal 0 (isoVar 1 z)] at h
    rw [variance_fun_id_gaussianReal] at h
    simpa only [isoVar,one_mul,NNReal.coe_mk] using h
  have hM (z : H) : MemLp (W z) 2 μ := (hW z).memLp IsGaussian.memLp_two_id
  have he := variance_add (hM x) (hM y)
  rw [← map_add, hvar, hvar, hvar, norm_add_sq_real] at he
  linarith only [he]

theorem stepNodeL2_inner {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    ⟪stepNodeL2 s,stepNodeL2 t⟫ = min s t := by
  have hs' : (stepNodeL2 s : ℝ → ℝ) =ᵐ[volume] stepNode s := MemLp.coeFn_toLp _
  have ht' : (stepNodeL2 t : ℝ → ℝ) =ᵐ[volume] stepNode t := MemLp.coeFn_toLp _
  rw [MeasureTheory.L2.inner_def]
  calc
    _ = ∫ x, stepNode (min s t) x := by
      apply integral_congr_ae
      filter_upwards [hs',ht'] with x hxs hxt
      rw [hxs,hxt]
      have hM : x ∈ Icc 0 (min s t) ↔ x ∈ Icc 0 s ∧ x ∈ Icc 0 t := by
        simp only [Set.mem_Icc,le_min_iff]
        tauto
      unfold stepNode
      by_cases h₁ : x ∈ Icc 0 s <;> by_cases h₂ : x ∈ Icc 0 t <;>
        simp [h₁,h₂,hM,Real.inner_apply]
    _ = min s t := by
      unfold stepNode
      rw [integral_indicator measurableSet_Icc]
      simp only [integral_const,Measure.real,Measure.restrict_apply MeasurableSet.univ,univ_inter,
        Real.volume_Icc,smul_eq_mul,mul_one,sub_zero,ENNReal.toReal_ofReal (le_min hs ht)]

set_option maxHeartbeats 350000 in
theorem isonormal_finite_hasGaussianLaw
    {Ω H I : Type*} [MeasurableSpace Ω] [SeminormedAddCommGroup H] [NormedSpace ℝ H]
    [Fintype I] (μ : Measure Ω) (W : H →ₗ[ℝ] (Ω → ℝ))
    (hW : ∀ x, HasLaw (W x) (gaussianReal 0 (isoVar 1 x)) μ) (f : I → H) :
    HasGaussianLaw (fun w i ↦ W (f i) w) μ := by
  classical
  let X := fun w i ↦ W (f i) w
  have hX : AEMeasurable X μ := AEMeasurable.of_eval fun i ↦ (hW (f i)).aemeasurable
  refine ⟨hX,⟨fun L ↦ ?_⟩⟩
  have hL (v : I → ℝ) : L v = ∑ i, v i * L (Pi.single i 1) := by
    conv_lhs => rw [← Finset.univ_sum_single v]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [show Pi.single i (v i) = v i • Pi.single i (1:ℝ) from by
      ext j
      by_cases h : j = i <;> simp [Pi.single_apply,h]]
    rw [map_smul]
    rfl
  let z := ∑ i, L (Pi.single i 1) • f i
  have hz : L ∘ X = W z := by
    funext w
    change L (X w) = W z w
    rw [hL]
    simp only [X,z,map_sum,map_smul,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,mul_comm]
  have hG : μ.map (W z) = gaussianReal (∫ w, W z w ∂μ) (Var[W z; μ]).toNNReal :=
    (hW z).hasGaussianLaw.map_eq_gaussianReal
  have hmL : Measurable L := L.continuous.measurable
  have hMap : (μ.map X).map L = μ.map (L ∘ X) :=
    AEMeasurable.map_map_of_aemeasurable hmL.aemeasurable hX
  have hInt : (∫ y, L y ∂(μ.map X)) = ∫ w, (L ∘ X) w ∂μ :=
    integral_map hX hmL.aestronglyMeasurable
  have hVar : Var[(L : (I → ℝ) → ℝ); μ.map X] = Var[L ∘ X; μ] :=
    variance_map hmL.aemeasurable hX
  change (μ.map X).map L = gaussianReal (∫ y, L y ∂(μ.map X))
    (Var[(L : (I → ℝ) → ℝ); μ.map X]).toNNReal
  rw [hMap,hInt,hVar,hz]
  exact hG

/-- The actual unsmoothed Gaussian scores use a pre-Brownian motion:
the interval indicators give the exact Brownian Gram matrix. -/
theorem isonormal_step_isPreBrownian
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : (Lp ℝ 2 (volume : Measure ℝ)) →ₗ[ℝ] (Ω → ℝ))
    (hW : ∀ x, HasLaw (W x) (gaussianReal 0 (isoVar 1 x)) μ) :
    IsPreBrownianReal (fun t : ℝ≥0 ↦ W (stepNodeL2 t)) μ := by
  apply IsGaussianProcess.isPreBrownianReal_of_covariance
  · exact ⟨fun I ↦ isonormal_finite_hasGaussianLaw μ W hW (fun i : I ↦ stepNodeL2 i.1)⟩
  · intro t
    simpa only [integral_id_gaussianReal] using (hW (stepNodeL2 t)).integral_eq
  · intro s t hst
    rw [isonormal_covariance μ W hW, stepNodeL2_inner (NNReal.coe_nonneg s) (NNReal.coe_nonneg t)]
    exact min_eq_left (by exact_mod_cast hst)

theorem stepNodeL2_norm_sq {t : ℝ} (ht : 0 ≤ t) : ‖stepNodeL2 t‖^2 = t := by
  rw [← real_inner_self_eq_norm_sq,stepNodeL2_inner ht ht,min_self]

theorem isoScore_step_eq_brownian_score
    {Ω : Type*} [MeasurableSpace Ω]
    (W : (Lp ℝ 2 (volume : Measure ℝ)) →ₗ[ℝ] (Ω → ℝ)) (k t : ℝ≥0) (w : Ω) :
    isoScore W k (stepNodeL2 t) w =
      Real.sqrt (k:ℝ) * W (stepNodeL2 t) w - (k:ℝ)*t/2 := by
  unfold isoScore isoVar
  push_cast
  rw [stepNodeL2_norm_sq (NNReal.coe_nonneg t)]

end CubeBrownian
#print axioms CubeBrownian.isonormal_step_isPreBrownian
#print axioms CubeBrownian.isoScore_step_eq_brownian_score
