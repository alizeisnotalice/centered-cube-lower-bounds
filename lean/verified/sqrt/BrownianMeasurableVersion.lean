import DriftedBrownianMaximum
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology
namespace CubeBrownian

theorem brownian_measurable_version {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B μ) :
    ∃ C : ℝ≥0 → Ω → ℝ, IsBrownianReal C μ ∧ (∀ t, Measurable (C t)) ∧
      ∀ᵐ w ∂μ, ∀ t, B t w = C t w := by
  classical
  let A (r k : ℕ) : Ω → ℝ :=
    (hB.toIsPreBrownianReal.aemeasurable (dyadicT 1 r k)).mk (B (dyadicT 1 r k))
  have hAm (r k : ℕ) : Measurable (A r k) :=
    (hB.toIsPreBrownianReal.aemeasurable (dyadicT 1 r k)).measurable_mk
  have hAe : ∀ᵐ w ∂μ, ∀ r k, B (dyadicT 1 r k) w = A r k w := by
    rw [ae_all_iff]
    intro r
    rw [ae_all_iff]
    intro k
    exact (hB.toIsPreBrownianReal.aemeasurable (dyadicT 1 r k)).ae_eq_mk
  let G : Set Ω := {w | Continuous (B · w) ∧ ∀ r k, B (dyadicT 1 r k) w = A r k w}
  have hg : ∀ᵐ w ∂μ, w ∈ G := by
    filter_upwards [hB.cont,hAe] with w hcont heq
    exact ⟨hcont,heq⟩
  let S := (toMeasurable μ Gᶜ)ᶜ
  have hSm : MeasurableSet S := (measurableSet_toMeasurable _ _).compl
  have hSG : S ⊆ G := by
    simpa only [S, compl_subset_comm] using subset_toMeasurable μ Gᶜ
  have hS : ∀ᵐ w ∂μ, w ∈ S := by
    rw [ae_iff]
    change μ Sᶜ = 0
    rw [show Sᶜ = toMeasurable μ Gᶜ by simp [S], measure_toMeasurable]
    exact ae_iff.mp hg
  let C (t : ℝ≥0) : Ω → ℝ := S.indicator (B t)
  have hEq : ∀ᵐ w ∂μ, ∀ t, B t w = C t w := hS.mono (fun w hw t ↦
    (indicator_of_mem hw (B t)).symm)
  have hM (t : ℝ≥0) : Measurable (C t) := by
    let F (r : ℕ) : Ω → ℝ := S.indicator (A r (dyadicBelowIndex 1 t r))
    have hFm (r : ℕ) : Measurable (F r) := (hAm _ _).indicator hSm
    apply measurable_of_tendsto_metrizable hFm
    apply tendsto_pi_nhds.mpr
    intro w
    by_cases hs : w ∈ S
    · have h := hSG hs
      change Continuous (B · w) ∧ ∀ r k, B (dyadicT 1 r k) w = A r k w at h
      simp only [F,C,indicator_of_mem hs,← h.2]
      exact h.1.continuousAt.tendsto.comp (dyadicBelow_tendsto (T:=1) (s:=t) one_pos)
    · simp only [F,C,indicator_of_notMem hs]
      exact tendsto_const_nhds
  refine ⟨C,⟨hB.toIsPreBrownianReal.congr (fun t ↦ hEq.mono (fun _ h ↦ h t)),?_⟩,hM,hEq⟩
  filter_upwards [hB.cont,hEq] with w hw h
  have he : (C · w) = (B · w) := funext (fun t ↦ (h t).symm)
  rwa [he]

theorem paperBrownian_exp_expectation_complete {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B μ)
    (T : ℝ≥0) (hT : 0 < T) :
    (∫ w, Real.exp (⨆ t : Icc (0:ℝ≥0) T, Real.sqrt 2 * B t w - (t.1:ℝ)) ∂μ) =
      maxExpFormula (T:ℝ) := by
  obtain ⟨C,hC,hmC,hEq⟩ := brownian_measurable_version μ hB
  rw [← paperBrownian_exp_expectation μ hC hmC T hT]
  apply integral_congr_ae
  filter_upwards [hEq] with w hw
  simp only [hw]

theorem paperBrownian_reflected_tail_complete {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B μ)
    (T : ℝ≥0) (hT : 0 < T) :
    HasReflectedTail μ (fun w ↦
      ⨆ t : Icc (0:ℝ≥0) T, Real.sqrt 2 * B t w - (t.1:ℝ)) (T:ℝ) := by
  obtain ⟨C,hC,hmC,hEq⟩ := brownian_measurable_version μ hB
  intro a ha
  have he : {w | a < ⨆ t : Icc (0:ℝ≥0) T, Real.sqrt 2 * B t w - (t.1:ℝ)} =ᵐ[μ]
      {w | a < ⨆ t : Icc (0:ℝ≥0) T, Real.sqrt 2 * C t w - (t.1:ℝ)} := by
    filter_upwards [hEq] with w hw
    simp only [hw]
  change μ {w | a < ⨆ t : Icc (0:ℝ≥0) T, Real.sqrt 2 * B t w - (t.1:ℝ)} = _
  rw [measure_congr he]
  exact paperBrownian_reflected_tail μ hC hmC T hT a ha

theorem paperBrownian_expectation_div_tendsto_one {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B μ) :
    Tendsto (fun T : ℝ≥0 ↦
      (∫ w, Real.exp (⨆ t : Icc (0:ℝ≥0) T, Real.sqrt 2 * B t w - (t.1:ℝ)) ∂μ) /
        (T:ℝ)) atTop (𝓝 1) := by
  have hc : Tendsto (fun T : ℝ≥0 ↦ (T:ℝ)) atTop atTop := by
    apply tendsto_atTop.mpr
    intro x
    filter_upwards [eventually_ge_atTop x.toNNReal] with T hT
    exact (Real.le_coe_toNNReal x).trans (by exact_mod_cast hT)
  apply (maxExpFormula_div_tendsto_one.comp hc).congr'
  filter_upwards [eventually_ge_atTop (1:ℝ≥0)] with T hT
  have hp : 0 < T := one_pos.trans_le hT
  dsimp only [Function.comp_apply]
  rw [paperBrownian_exp_expectation_complete μ hB T hp]
end CubeBrownian
#print axioms CubeBrownian.paperBrownian_exp_expectation_complete
#print axioms CubeBrownian.paperBrownian_reflected_tail_complete
#print axioms CubeBrownian.paperBrownian_expectation_div_tendsto_one
