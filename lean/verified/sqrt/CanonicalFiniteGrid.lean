import FiniteBrownianLaw

namespace CubeBrownian
open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology ProbabilityTheory RealInnerProductSpace
set_option maxHeartbeats 1250000
set_option linter.style.haveILetI false

def gridSpan {H I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f : I→H) : Submodule ℝ H := Submodule.span ℝ (Set.range f)

instance gridSpan_finiteDimensional {H I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [Finite I] (f : I→H) : FiniteDimensional ℝ (gridSpan f) :=
  FiniteDimensional.span_of_finite ℝ (Set.finite_range f)

def gridSpanNode {H I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f : I→H) (i : I) : gridSpan f := ⟨f i,Submodule.subset_span (Set.mem_range_self i)⟩

noncomputable def canonicalFiniteGridExp {H I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [Fintype I] (f : I→H) (k : ℝ≥0) : ℝ :=
  letI : MeasurableSpace (gridSpan f) := borel _
  letI : BorelSpace (gridSpan f) := ⟨rfl⟩
  ∫ w, Real.exp (⨆ i, isoScore (pairedSpanIsonormal (gridSpan f)) k (gridSpanNode f i) w)
    ∂(stdGaussian (gridSpan f))

theorem finite_isonormal_expMax_eq_canonical {Ω H H' I : Type*}
    [MeasurableSpace Ω] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup H'] [InnerProductSpace ℝ H'] [Fintype I]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : H →ₗ[ℝ] (Ω→ℝ))
    (hW : ∀ x, HasLaw (W x) (gaussianReal 0 (isoVar 1 x)) μ)
    (f : I→H) (g : I→H') (hG : ∀ i j, ⟪f i,f j⟫=⟪g i,g j⟫) (k : ℝ≥0) :
    (∫ w, Real.exp (⨆ i, isoScore W k (f i) w) ∂μ)=canonicalFiniteGridExp g k := by
  let S := gridSpan g
  letI : MeasurableSpace S := borel _
  letI : BorelSpace S := ⟨rfl⟩
  let V := pairedSpanIsonormal S
  let ν := stdGaussian S
  let G : I→S := gridSpanNode g
  have hV (x : S) := pairedSpanIsonormal_hasLaw x
  have hNorm (i : I) : ‖f i‖^2=‖G i‖^2 := by
    rw [←real_inner_self_eq_norm_sq,←real_inner_self_eq_norm_sq,hG]
    rfl
  have hX := isonormal_finite_hasGaussianLaw μ W hW f
  have hY := isonormal_finite_hasGaussianLaw ν V hV G
  have hM i : (∫ w, W (f i) w ∂μ)=(∫ w, V (G i) w ∂ν) := by
    rw [(hW (f i)).integral_eq,(hV (G i)).integral_eq,integral_id_gaussianReal,integral_id_gaussianReal]
  have hC i j : cov[W (f i),W (f j);μ]=cov[V (G i),V (G j);ν] := by
    rw [isonormal_covariance μ W hW,isonormal_covariance ν V hV,hG]
    rfl
  have H := gaussian_finite_map_eq_of_moments μ ν (fun i => W (f i)) (fun i=>V (G i)) hX hY hM hC
  let Φ : (I→ℝ)→ℝ := fun z => Real.exp (⨆ i, Real.sqrt (k:ℝ)*z i-(k:ℝ)*‖f i‖^2/2)
  have hΦ : Measurable Φ := Real.measurable_exp.comp (Measurable.iSup fun i =>
    (measurable_const.mul (measurable_pi_apply i)).sub_const _)
  have F : (fun x => Real.exp (⨆ i, isoScore W k (f i) x))=fun x => Φ (fun i => W (f i) x) := by
    funext x
    unfold Φ isoScore isoVar
    push_cast
    rfl
  have E : (fun x => Real.exp (⨆ i, isoScore V k (G i) x))=fun x => Φ (fun i => V (G i) x) := by
    funext x
    unfold Φ isoScore isoVar
    push_cast
    simp_rw [hNorm]
  change (∫ w, Real.exp (⨆ i, isoScore W k (f i) w) ∂μ)=∫ w, Real.exp (⨆ i, isoScore V k (G i) w) ∂ν
  rw [F,E,←integral_map hX.aemeasurable hΦ.aestronglyMeasurable,H,
    integral_map hY.aemeasurable hΦ.aestronglyMeasurable]

theorem canonical_stepGrid_eq_Brownian {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    (μ : Measure Ω) (B : ℝ≥0→Ω→ℝ) (hB : IsPreBrownianReal B μ) (t : I→ℝ≥0) (k : ℝ≥0) :
    canonicalFiniteGridExp (fun i => stepNodeL2 (t i)) k =
      ∫ x, Real.exp (⨆ i, Real.sqrt (k:ℝ)*B (t i) x-(k:ℝ)*(t i:ℝ)/2) ∂μ := by
  let f (i : I) := stepNodeL2 (t i)
  let S := gridSpan f
  letI : MeasurableSpace S := borel _
  letI : BorelSpace S := ⟨rfl⟩
  let V := pairedSpanIsonormal S
  let ν := stdGaussian S
  let G : I→S := gridSpanNode f
  have hV (x : S) := pairedSpanIsonormal_hasLaw x
  have hGram i j : ⟪G i,G j⟫=min (t i:ℝ) (t j:ℝ) :=
    stepNodeL2_inner (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)
  exact paired_raw_grid_expectation_eq μ B hB ν V hV t G hGram k

#print axioms finite_isonormal_expMax_eq_canonical
#print axioms canonical_stepGrid_eq_Brownian
end CubeBrownian
