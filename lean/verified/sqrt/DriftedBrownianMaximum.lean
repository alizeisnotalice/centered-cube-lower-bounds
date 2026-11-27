import FiniteTiltTransport
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
namespace CubeBrownian

noncomputable def driftedCentered {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (w : Ω) (t : ℝ≥0) : ℝ :=
  centeredScaled B w t - (t:ℝ)

theorem dyadicIncrements_drift_law {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)
    (hmB : ∀ t, Measurable (B t)) (T : ℝ≥0) (r : ℕ) :
    let h := T/(2:ℝ≥0)^r
    (μ.map fun w ↦ dyadicIncrements T r (driftedCentered B w)) =
      Measure.pi (fun _ : Fin (2^r) ↦ gaussianReal (-(h:ℝ)) (2*h)) := by
  dsimp only
  let h := T/(2:ℝ≥0)^r
  let D := fun w ↦ dyadicIncrements T r (centeredScaled B w)
  let S := fun (x : Fin (2^r) → ℝ) i ↦ x i + -(h:ℝ)
  have hmF (s : ℝ≥0) : Measurable (fun w ↦ centeredScaled B w s) :=
    measurable_const.mul ((hmB s).sub (hmB 0))
  have hmD : Measurable D := measurable_pi_iff.mpr (fun i ↦ (hmF _).sub (hmF _))
  have hmS : Measurable S :=
    measurable_pi_iff.mpr (fun i ↦ (measurable_pi_apply i).add measurable_const)
  have he : (fun w ↦ dyadicIncrements T r (driftedCentered B w)) = S ∘ D := by
    funext w i
    let t := dyadicT T r ((i:ℕ)+1)
    let s := dyadicT T r i
    have d : (t:ℝ)-(s:ℝ) = (h:ℝ) := dyadicT_succ_sub T r i
    change (centeredScaled B w t-(t:ℝ))-(centeredScaled B w s-(s:ℝ)) =
      centeredScaled B w t-centeredScaled B w s + -(h:ℝ)
    linarith only [d]
  rw [he,← Measure.map_map hmS hmD,dyadicIncrements_centered_law μ hB T r]
  let shift : ℝ → ℝ := fun x ↦ x + -(h:ℝ)
  have hmShift : Measurable shift := by dsimp [shift]; fun_prop
  have hGauss : (gaussianReal 0 (2*h)).map shift = gaussianReal (-(h:ℝ)) (2*h) := by
    simpa only [shift,zero_add] using gaussianReal_map_add_const (μ:=0) (v:=2*h) (-(h:ℝ))
  have : ∀ _ : Fin (2^r), SigmaFinite ((gaussianReal 0 (2*h)).map shift) := by
    intro _
    rw [hGauss]
    infer_instance
  change (Measure.pi (fun _ : Fin (2^r) ↦ gaussianReal 0 (2*h))).map
    (fun x i ↦ shift (x i)) = _
  rw [Measure.pi_map_pi (fun _ ↦ hmShift.aemeasurable)]
  simp only [hGauss,h]

theorem measurableSet_dyadicHits {Ω : Type*} [MeasurableSpace Ω] (T : ℝ≥0)
    (r : ℕ) (a : ℝ) (F : Ω → ℝ≥0 → ℝ) (hmF : ∀ t, Measurable (fun w ↦ F w t)) :
    MeasurableSet {w | dyadicHits T r a (F w)} := by
  have he : {w | dyadicHits T r a (F w)} =
    ⋃ k : ℕ, {w | k ≤ 2^r ∧ a < F w (dyadicT T r k)} := by
    ext w
    simp [dyadicHits]
  rw [he]
  apply MeasurableSet.iUnion
  intro k
  by_cases hk : k ≤ 2^r
  · simpa only [hk,true_and] using
      (measurableSet_lt measurable_const (hmF (dyadicT T r k)) :
        MeasurableSet {w | a < F w (dyadicT T r k)})
  · simp [hk]

theorem sampledSup_grid_spec {Ω : Type*} (F : Ω → ℝ≥0 → ℝ) (w : Ω)
    {T : ℝ≥0} (_hT : 0 < T) (hC : Continuous (F w)) (h0 : F w 0 = 0) :
    0 ≤ sampledSup (fun k ω ↦ F ω (gridSample T k)) w ∧
      ∀ a : ℝ, a < sampledSup (fun k ω ↦ F ω (gridSample T k)) w ↔
        ∃ r, dyadicHits T r a (F w) := by
  have hBd : BddAbove (F w '' Icc 0 T) := (isCompact_Icc.image hC).bddAbove
  have hS : BddAbove (range (fun k ↦ F w (gridSample T k))) := hBd.mono (by
    rintro _ ⟨k,rfl⟩
    exact ⟨_,⟨zero_le, gridSample_le T k⟩,rfl⟩)
  have H : sampledSup (fun k ω ↦ F ω (gridSample T k)) w = ⨆ k, F w (gridSample T k) := by
    have hw : w ∈ boundedSamples (fun k ω ↦ F ω (gridSample T k)) := hS
    simp only [sampledSup,indicator_of_mem hw]
  rw [H]
  constructor
  · have hz := le_ciSup hS (Nat.pair 0 0)
    rwa [gridSample_pair T 0 0 (by omega),dyadicT_zero,h0] at hz
  · intro a
    rw [lt_ciSup_iff hS]
    constructor
    · rintro ⟨k,hk⟩
      exact ⟨k.unpair.1,_,min_le_right ..,hk⟩
    · rintro ⟨r,k,hk,hHit⟩
      exact ⟨Nat.pair r k,by simpa only [gridSample_pair T r k hk] using hHit⟩

noncomputable def driftedBrownianGridMax {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) : Ω → ℝ :=
  sampledSup (fun k w ↦ driftedCentered B w (gridSample T k))

theorem driftedBrownianGridMax_map_eq {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B μ)
    (hmB : ∀ t, Measurable (B t)) (T : ℝ≥0) (hT : 0 < T) :
    μ.map (driftedBrownianGridMax B T) =
      (μ.tilted (fun w ↦ -(centeredScaled B w T/2))).map (brownianGridMax B T) := by
  let ν := μ.tilted (fun w ↦ -(centeredScaled B w T/2))
  let f := centeredScaled B
  let g := driftedCentered B
  have hmF (t : ℝ≥0) : Measurable (fun w ↦ f w t) :=
    measurable_const.mul ((hmB t).sub (hmB 0))
  have hmG (t : ℝ≥0) : Measurable (fun w ↦ g w t) := (hmF t).sub measurable_const
  have mf := measurable_brownianGridMax B hmB T
  have mg : Measurable (driftedBrownianGridMax B T) := measurable_sampledSup _ (fun k ↦ hmG _)
  have hZ : HasLaw (fun w ↦ f w T) (gaussianReal 0 (2*T)) μ := centeredScaled_law hB.toIsPreBrownianReal T
  have hx : Integrable (fun z ↦ Real.exp (-(z/2))) (gaussianReal 0 (2*T)) := by
    have he : (fun z : ℝ ↦ Real.exp (-(z/2))) = (fun z ↦ Real.exp ((-1/2)*z)) := by
      funext z; congr 1; ring
    rw [he]
    exact integrable_exp_mul_gaussianReal _
  have hmExp : Measurable (fun z : ℝ ↦ Real.exp (-(z/2))) := by fun_prop
  have hInt : Integrable (fun w ↦ Real.exp (-(f w T/2))) μ := by
    apply (integrable_map_measure hmExp.aestronglyMeasurable (hmF T).aemeasurable).mp
    rw [hZ.map_eq]
    exact hx
  let _ : IsProbabilityMeasure μ := hB.toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
  let _ : IsProbabilityMeasure ν := isProbabilityMeasure_tilted hInt
  have hAC : ν ≪ μ := tilted_absolutelyContinuous _ _
  have hcf : ∀ᵐ w ∂μ, Continuous (f w) := hB.cont.mono (fun w h ↦ continuous_const.mul (h.sub continuous_const))
  have hcg : ∀ᵐ w ∂μ, Continuous (g w) := hcf.mono (fun w h ↦ h.sub continuous_subtype_val)
  have hC0 (w : Ω) : g w 0 = 0 := by
    change f w 0 - ((0:ℝ≥0):ℝ) = 0
    simp [f,centeredScaled_zero]
  have hspecf := hAC.ae_le (hcf.mono (fun w h ↦ sampledSup_grid_spec f w hT h (centeredScaled_zero B w)))
  have hspecg := hcg.mono (fun w h ↦ sampledSup_grid_spec g w hT h (hC0 w))
  have htails (a : ℝ) : μ {w | a < driftedBrownianGridMax B T w} =
      ν {w | a < brownianGridMax B T w} := by
    by_cases ha : 0 ≤ a
    · let E (r : ℕ) : Set Ω := {w | dyadicHits T r a (g w)}
      let F (r : ℕ) : Set Ω := {w | dyadicHits T r a (f w)}
      have hE : Monotone E := fun _ _ h w hw ↦ dyadicHits_mono T a (g w) h hw
      have hF : Monotone F := fun _ _ h w hw ↦ dyadicHits_mono T a (f w) h hw
      have hgAE : {w | a < driftedBrownianGridMax B T w} =ᵐ[μ] (⋃ r, E r) := by
        filter_upwards [hspecg] with w hw
        simpa only [driftedBrownianGridMax,E,mem_ofPred_eq,mem_iUnion,g] using hw.2 a
      have hfAE : {w | a < brownianGridMax B T w} =ᵐ[ν] (⋃ r, F r) := by
        filter_upwards [hspecf] with w hw
        simpa only [brownianGridMax,F,mem_ofPred_eq,mem_iUnion,f] using hw.2 a
      rw [measure_congr hgAE,measure_congr hfAE]
      have hEq (r : ℕ) : μ (E r) = ν (F r) := by
        let Dg (w : Ω) := dyadicIncrements T r (g w)
        let Df (w : Ω) := dyadicIncrements T r (f w)
        let S : Set (Fin (2^r) → ℝ) := {x | ∃ k, a < partialSum k x}
        have hmS : MeasurableSet S := by
          change MeasurableSet {x | ∃ k, a < partialSum k x}
          rw [← firstCross_iUnion]
          exact .iUnion (measurable_firstCross a)
        have hmDg : Measurable Dg := measurable_pi_iff.mpr (fun i ↦ (hmG _).sub (hmG _))
        have hmDf : Measurable Df := measurable_pi_iff.mpr (fun i ↦ (hmF _).sub (hmF _))
        have he : E r = Dg ⁻¹' S := by
          ext w
          exact dyadicHits_iff_prefix T r a ha (g w) (hC0 w)
        have hf : F r = Df ⁻¹' S := by
          ext w
          exact dyadicHits_iff_prefix T r a ha (f w) (centeredScaled_zero B w)
        rw [he,hf,← Measure.map_apply hmDg hmS,← Measure.map_apply hmDf hmS]
        have h₁ := dyadicIncrements_drift_law μ hB.toIsPreBrownianReal hmB T r
        have h₂ := dyadicIncrements_tilt_law μ hB.toIsPreBrownianReal hmB T hT r
        dsimp only at h₁ h₂
        rw [h₁,h₂]
      have hl := tendsto_measure_iUnion_atTop (μ:=μ) hE
      have hr := tendsto_measure_iUnion_atTop (μ:=ν) hF
      exact tendsto_nhds_unique (hl.congr hEq) hr
    · have hgAE : {w | a < driftedBrownianGridMax B T w} =ᵐ[μ] (univ : Set Ω) := by
        filter_upwards [hspecg] with w hw
        exact iff_true_intro ((lt_of_not_ge ha).trans_le hw.1)
      have hfAE : {w | a < brownianGridMax B T w} =ᵐ[ν] (univ : Set Ω) := by
        filter_upwards [hspecf] with w hw
        exact iff_true_intro ((lt_of_not_ge ha).trans_le hw.1)
      simp only [measure_congr hgAE,measure_congr hfAE,measure_univ]
  apply Measure.ext_of_Iic
  intro z
  have hEq := htails z
  change μ (driftedBrownianGridMax B T ⁻¹' Ioi z) =
    ν (brownianGridMax B T ⁻¹' Ioi z) at hEq
  rw [← Measure.map_apply mg measurableSet_Ioi,← Measure.map_apply mf measurableSet_Ioi] at hEq
  change (μ.map (driftedBrownianGridMax B T)) (Iic z) = (ν.map (brownianGridMax B T)) (Iic z)
  simp only [← compl_Ioi, prob_compl_eq_one_sub measurableSet_Ioi,hEq]

theorem driftedBrownianGridMax_exp_expectation {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B μ)
    (hmB : ∀ t, Measurable (B t)) (T : ℝ≥0) (hT : 0 < T) :
    (∫ w, Real.exp (driftedBrownianGridMax B T w) ∂μ) = maxExpFormula (T:ℝ) := by
  let ν := μ.tilted (fun w ↦ -(centeredScaled B w T/2))
  have mg : Measurable (driftedBrownianGridMax B T) := measurable_sampledSup _
    (fun k ↦ (measurable_const.mul ((hmB _).sub (hmB 0))).sub measurable_const)
  have mf := measurable_brownianGridMax B hmB T
  have eG := integral_map (μ:=μ) mg.aemeasurable Real.measurable_exp.aestronglyMeasurable
  have eF := integral_map (μ:=ν) mf.aemeasurable Real.measurable_exp.aestronglyMeasurable
  rw [← eG,driftedBrownianGridMax_map_eq μ hB hmB T hT,eF]
  exact brownianGridMax_terminalTilt μ hB hmB T hT

theorem driftedBrownianGridMax_ae_eq_pathSup {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B μ)
    (T : ℝ≥0) (hT : 0 < T) :
    driftedBrownianGridMax B T =ᵐ[μ] fun w ↦
      ⨆ t : Icc (0:ℝ≥0) T, Real.sqrt 2 * B t w - (t.1:ℝ) := by
  filter_upwards [hB.cont, hB.toIsPreBrownianReal.eval_zero_ae_eq_zero] with w hC h0B
  let g := driftedCentered B w
  have hg : Continuous g := (continuous_const.mul (hC.sub continuous_const)).sub continuous_subtype_val
  have hz : g 0 = 0 := by simp [g,driftedCentered,centeredScaled_zero]
  have hh := (sampledSup_grid_spec (driftedCentered B) w hT hg hz).2
  have hS : BddAbove (range (fun t : Icc (0:ℝ≥0) T ↦ g t)) := by
    have hc : BddAbove (g '' Icc 0 T) := (isCompact_Icc.image hg).bddAbove
    apply hc.mono
    rintro _ ⟨t,rfl⟩
    exact ⟨t,t.2,rfl⟩
  let _ : Nonempty (Icc (0:ℝ≥0) T) := ⟨⟨0,le_rfl,zero_le⟩⟩
  have he (a : ℝ) : a < driftedBrownianGridMax B T w ↔ a < ⨆ t : Icc (0:ℝ≥0) T, g t := by
    rw [lt_ciSup_iff hS]
    change (a < sampledSup (fun k ω ↦ driftedCentered B ω (gridSample T k)) w) ↔ _
    rw [hh,dyadicHits_iff_exists hT a g hg]
    exact ⟨fun ⟨t,ht,h⟩ ↦ ⟨⟨t,zero_le,ht⟩,h⟩,fun ⟨t,h⟩ ↦ ⟨t,t.2.2,h⟩⟩
  have heq : driftedBrownianGridMax B T w = ⨆ t : Icc (0:ℝ≥0) T, g t := by
    apply le_antisymm
    · by_contra! h
      exact (lt_irrefl _ ) ((he _).mp h)
    · by_contra! h
      exact (lt_irrefl _ ) ((he _).mpr h)
  rw [heq]
  simp [g,driftedCentered,centeredScaled,h0B]

theorem paperBrownian_exp_expectation {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B μ)
    (hmB : ∀ t, Measurable (B t)) (T : ℝ≥0) (hT : 0 < T) :
    (∫ w, Real.exp (⨆ t : Icc (0:ℝ≥0) T, Real.sqrt 2 * B t w - (t.1:ℝ)) ∂μ) =
      maxExpFormula (T:ℝ) := by
  rw [← driftedBrownianGridMax_exp_expectation μ hB hmB T hT]
  apply integral_congr_ae
  exact (driftedBrownianGridMax_ae_eq_pathSup μ hB T hT).mono (fun _ h ↦ congrArg Real.exp h.symm)

theorem paperBrownian_reflected_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B μ)
    (hmB : ∀ t, Measurable (B t)) (T : ℝ≥0) (hT : 0 < T) :
    HasReflectedTail μ (fun w ↦
      ⨆ t : Icc (0:ℝ≥0) T, Real.sqrt 2 * B t w - (t.1:ℝ)) (T:ℝ) := by
  let ν := μ.tilted (fun w ↦ -(centeredScaled B w T/2))
  let F := brownianGridMax B T
  let G := driftedBrownianGridMax B T
  let Z := fun w ↦ centeredScaled B w T
  let P := fun w ↦ ⨆ t : Icc (0:ℝ≥0) T, Real.sqrt 2 * B t w - (t.1:ℝ)
  have hmZ : Measurable Z := measurable_const.mul ((hmB T).sub (hmB 0))
  have hmF : Measurable F := measurable_brownianGridMax B hmB T
  have hmG : Measurable G := measurable_sampledSup _
    (fun _ ↦ (measurable_const.mul ((hmB _).sub (hmB 0))).sub measurable_const)
  have hZ := centeredScaled_law hB.toIsPreBrownianReal T
  have hmExp : Measurable (fun z : ℝ ↦ Real.exp (-(z/2))) := by fun_prop
  have hInt : Integrable (fun w ↦ Real.exp (-(Z w/2))) μ := by
    apply (integrable_map_measure hmExp.aestronglyMeasurable hmZ.aemeasurable).mp
    rw [hZ.map_eq]
    have he : (fun z : ℝ ↦ Real.exp (-(z/2))) = (fun z ↦ Real.exp ((-1/2)*z)) := by
      funext z; congr 1; ring
    rw [he]
    exact integrable_exp_mul_gaussianReal _
  let _ : IsProbabilityMeasure μ := hB.toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
  let _ : IsProbabilityMeasure ν := isProbabilityMeasure_tilted hInt
  have hJoint : JointEndpointReflection μ Z F T :=
    brownian_jointEndpointReflection μ hB hmB T hT F hmF
      (hB.cont.mono (fun w hw x _ ↦ (brownianGridMax_spec B w hT hw).2 x))
  have hTail : HasReflectedTail ν F (T:ℝ) :=
    reflected_tail_of_endpoint_split ν F T hT
      (tilted_endpoint_split_of_joint_reflection μ Z F T hmZ hmF hZ.map_eq hJoint)
  intro x hx
  have hh := hTail x hx
  have hAE : {w | x < P w} =ᵐ[μ] {w | x < G w} := by
    filter_upwards [driftedBrownianGridMax_ae_eq_pathSup μ hB T hT] with w hw
    change G w = P w at hw
    rw [hw]
  change μ {w | x < P w} = _
  rw [measure_congr hAE]
  change μ (G ⁻¹' Ioi x) = _
  rw [← Measure.map_apply hmG measurableSet_Ioi, driftedBrownianGridMax_map_eq μ hB hmB T hT]
  change (ν.map F) (Ioi x) = _
  rw [Measure.map_apply hmF measurableSet_Ioi]
  exact hh
end CubeBrownian
#print axioms CubeBrownian.paperBrownian_reflected_tail
#print axioms CubeBrownian.paperBrownian_exp_expectation
