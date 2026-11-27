import PairedSpanIsonormal
import IsonormalBrownianLaw

namespace CubeBrownian
open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology ProbabilityTheory RealInnerProductSpace
set_option maxHeartbeats 1200000

theorem gaussian_finite_map_eq_of_moments {Ω Ω' I : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] [Fintype I] (μ : Measure Ω) (ν : Measure Ω')
    (X : I→Ω→ℝ) (Y : I→Ω'→ℝ)
    (hX : HasGaussianLaw (fun w i => X i w) μ) (hY : HasGaussianLaw (fun w i => Y i w) ν)
    (hm : ∀ i, (∫ w, X i w ∂μ)=(∫ w, Y i w ∂ν))
    (hc : ∀ i j, cov[X i,X j;μ]=cov[Y i,Y j;ν]) :
    μ.map (fun w i => X i w)=ν.map (fun w i => Y i w) := by
  let _ : IsProbabilityMeasure μ := hX.isProbabilityMeasure
  let _ : IsProbabilityMeasure ν := hY.isProbabilityMeasure
  let M : (I→ℝ) ≃ᵐ EuclideanSpace ℝ I := MeasurableEquiv.toLp 2 (I→ℝ)
  apply M.map_measurableEquiv_injective
  rw [AEMeasurable.map_map_of_aemeasurable M.measurable.aemeasurable hX.aemeasurable,
    AEMeasurable.map_map_of_aemeasurable M.measurable.aemeasurable hY.aemeasurable]
  change μ.map (fun w => WithLp.toLp 2 (fun i => X i w)) =
   ν.map (fun w => WithLp.toLp 2 (fun i => Y i w))
  have Xg := hX.toLp_pi 2
  have Yg := hY.toLp_pi 2
  let _ := Xg.isGaussian_map
  let _ := Yg.isGaussian_map
  apply IsGaussian.ext
  · rw [integral_map Xg.aemeasurable aestronglyMeasurable_id,integral_map Yg.aemeasurable aestronglyMeasurable_id]
    simp only [id_eq]
    apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : I=>ℝ)).injective
    funext i
    let L : EuclideanSpace ℝ I→L[ℝ] ℝ := EuclideanSpace.proj i
    change L (∫ w, WithLp.toLp 2 (fun j => X j w) ∂μ)=
      L (∫ w, WithLp.toLp 2 (fun j => Y j w) ∂ν)
    exact (L.integral_comp_comm Xg.integrable).symm.trans
      ((hm i).trans (L.integral_comp_comm Yg.integrable))
  · ext a b
    rw [covarianceBilin_apply_pi (fun i => (hX.eval i).memLp_two),
      covarianceBilin_apply_pi (fun i => (hY.eval i).memLp_two)]
    simp_rw [hc]

theorem preBrownian_arbitrary_fin_hasGaussianLaw {Ω I : Type*} [MeasurableSpace Ω]
    [Fintype I] (μ : Measure Ω) (B : ℝ≥0→Ω→ℝ)
    (hB : IsPreBrownianReal B μ) (t : I→ℝ≥0) :
    HasGaussianLaw (fun w i => B (t i) w) μ := by
  classical
  let J := (Finset.univ : Finset I).image t
  let T (i : I) : J := ⟨t i,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩
  let F : (J→ℝ) →L[ℝ] (I→ℝ) := ContinuousLinearMap.pi (fun i => ContinuousLinearMap.proj (T i))
  exact (hB.isGaussianProcess.hasGaussianLaw J).map F

/-- Real-law uniqueness for any finite set of raw step nodes in a finite span;
no Gaussian realization is needed outside that span. -/
theorem paired_raw_grid_expectation_eq {Ω H I : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Fintype I]
    (μ : Measure Ω) (B : ℝ≥0→Ω→ℝ) (hB : IsPreBrownianReal B μ)
    {Ω' : Type*} [MeasurableSpace Ω'] (ν : Measure Ω') [IsProbabilityMeasure ν]
    (W : H →ₗ[ℝ] (Ω'→ℝ))
    (hW : ∀ x, HasLaw (W x) (gaussianReal 0 (isoVar 1 x)) ν)
    (t : I→ℝ≥0) (g : I→H) (hGram : ∀ i j, ⟪g i,g j⟫=min (t i:ℝ) (t j:ℝ)) (k : ℝ≥0) :
    (∫ x, Real.exp (⨆ i, isoScore W k (g i) x) ∂ν) =
      ∫ x, Real.exp (⨆ i, Real.sqrt (k:ℝ)*B (t i) x-(k:ℝ)*(t i:ℝ)/2) ∂μ := by
  have hN i : ‖g i‖^2=(t i:ℝ) := by rw [←real_inner_self_eq_norm_sq,hGram,min_self]
  have hX := isonormal_finite_hasGaussianLaw ν W hW g
  have hY := preBrownian_arbitrary_fin_hasGaussianLaw μ B hB t
  have hM i : (∫ w, W (g i) w ∂ν)=(∫ w, B (t i) w ∂μ) := by
    rw [(hW (g i)).integral_eq,integral_id_gaussianReal,hB.integral_eval]
  have hC i j : cov[W (g i),W (g j);ν]=cov[B (t i),B (t j);μ] := by
    rw [isonormal_covariance ν W hW,hGram,hB.covariance_eval]
    exact (NNReal.coe_min _ _).symm
  have H := gaussian_finite_map_eq_of_moments ν μ (fun i => W (g i)) (fun i=>B (t i)) hX hY hM hC
  let Φ : (I→ℝ)→ℝ := fun z => Real.exp (⨆ i, Real.sqrt (k:ℝ)*z i-(k:ℝ)*(t i:ℝ)/2)
  have hΦ : Measurable Φ := Real.measurable_exp.comp (Measurable.iSup fun i =>
    (measurable_const.mul (measurable_pi_apply i)).sub_const _)
  have F : (fun x => Real.exp (⨆ i, isoScore W k (g i) x))=fun x => Φ (fun i => W (g i) x) := by
    funext x
    unfold Φ
    congr 1
    congr 1
    funext i
    unfold isoScore isoVar
    push_cast
    rw [hN i]
  rw [F,←integral_map hX.aemeasurable hΦ.aestronglyMeasurable,H,
    integral_map hY.aemeasurable hΦ.aestronglyMeasurable]

#print axioms gaussian_finite_map_eq_of_moments
#print axioms paired_raw_grid_expectation_eq
end CubeBrownian
