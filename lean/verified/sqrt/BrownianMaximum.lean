import BrownianJointReflection
import CountableSupremum
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology
namespace CubeBrownian

noncomputable def gridSample (T : ℝ≥0) (k : ℕ) : ℝ≥0 :=
  dyadicT T k.unpair.1 (min k.unpair.2 (2^k.unpair.1))

theorem gridSample_le (T : ℝ≥0) (k : ℕ) : gridSample T k ≤ T := by
  simpa only [gridSample,dyadicT_last] using
    dyadicT_mono T k.unpair.1 (min_le_right k.unpair.2 (2^k.unpair.1))

theorem gridSample_pair (T : ℝ≥0) (r k : ℕ) (hk : k ≤ 2^r) :
    gridSample T (Nat.pair r k) = dyadicT T r k := by simp [gridSample, min_eq_left hk]

def boundedSamples {Ω : Type*} (F : ℕ → Ω → ℝ) : Set Ω :=
  {w | BddAbove (range (fun n ↦ F n w))}

theorem measurableSet_boundedSamples {Ω : Type*} [MeasurableSpace Ω]
    (F : ℕ → Ω → ℝ) (hmF : ∀ n, Measurable (F n)) :
    MeasurableSet (boundedSamples F) := by
  have he : boundedSamples F = ⋃ n : ℕ, ⋂ k : ℕ, {w | F k w ≤ (n:ℝ)} := by
    ext w
    simp only [boundedSamples, mem_ofPred_eq, mem_iUnion,mem_iInter]
    constructor
    · rintro ⟨a,ha⟩
      obtain ⟨n,hn⟩ := exists_nat_ge a
      exact ⟨n,fun k ↦ (ha (mem_range_self k)).trans hn⟩
    · rintro ⟨n,hn⟩
      exact ⟨n,fun _ hx ↦ by obtain ⟨k,rfl⟩ := hx; exact hn k⟩
  rw [he]
  exact .iUnion (fun _ ↦ .iInter (fun k ↦ measurableSet_le (hmF k) measurable_const))

noncomputable def sampledSup {Ω : Type*} (F : ℕ → Ω → ℝ) (w : Ω) : ℝ := by
  classical
  exact ⨆ n, (boundedSamples F).indicator (F n) w

theorem measurable_sampledSup {Ω : Type*} [MeasurableSpace Ω]
    (F : ℕ → Ω → ℝ) (hmF : ∀ n, Measurable (F n)) :
    Measurable (sampledSup F) := by
  apply measurable_nat_sup _ (fun n ↦ (hmF n).indicator (measurableSet_boundedSamples F hmF))
  intro w
  by_cases hw : w ∈ boundedSamples F
  · rw [show (fun k ↦ (boundedSamples F).indicator (F k) w) = (fun k ↦ F k w) from funext (fun k ↦ indicator_of_mem hw (F k))]
    exact hw
  · simp only [indicator_of_notMem hw]
    exact ⟨0,fun _ hy ↦ by obtain ⟨k,rfl⟩ := hy; exact le_rfl⟩

noncomputable def brownianGridMax {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) : Ω → ℝ :=
  sampledSup (fun k w ↦ centeredScaled B w (gridSample T k))

theorem measurable_brownianGridMax {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (hmB : ∀ t, Measurable (B t)) (T : ℝ≥0) :
    Measurable (brownianGridMax B T) :=
  measurable_sampledSup _ (fun k ↦ measurable_const.mul ((hmB (gridSample T k)).sub (hmB 0)))

theorem brownianGridMax_spec {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (w : Ω)
    {T : ℝ≥0} (hT : 0 < T) (hC : Continuous (B · w)) :
    0 ≤ brownianGridMax B T w ∧
      ∀ a : ℝ, a < brownianGridMax B T w ↔ ∃ t ≤ T, a < centeredScaled B w t := by
  let f := centeredScaled B w
  have hf : Continuous f := continuous_const.mul (hC.sub continuous_const)
  have hBd : BddAbove (f '' Icc 0 T) := (isCompact_Icc.image hf).bddAbove
  have hS : BddAbove (range (fun k ↦ f (gridSample T k))) := hBd.mono (by
    rintro _ ⟨k,rfl⟩
    exact ⟨_,⟨zero_le, gridSample_le T k⟩,rfl⟩)
  have H : brownianGridMax B T w = ⨆ k, f (gridSample T k) := by
    have hw : w ∈ boundedSamples (fun k w ↦ centeredScaled B w (gridSample T k)) := hS
    simp only [brownianGridMax,sampledSup,indicator_of_mem hw,f]
  rw [H]
  constructor
  · have hz := le_ciSup hS (Nat.pair 0 0)
    rwa [gridSample_pair T 0 0 (by omega),dyadicT_zero,show f 0 = 0 from centeredScaled_zero B w] at hz
  · intro a
    rw [lt_ciSup_iff hS]
    constructor
    · rintro ⟨k,hk⟩
      exact ⟨_,gridSample_le T k,hk⟩
    · intro h
      obtain ⟨r,k,hk,hHit⟩ := (dyadicHits_iff_exists hT a f hf).mpr h
      exact ⟨Nat.pair r k,by simpa only [gridSample_pair T r k hk] using hHit⟩

theorem brownianGridMax_terminalTilt {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B μ)
    (hmB : ∀ t, Measurable (B t)) (T : ℝ≥0) (hT : 0 < T) :
    (∫ w, Real.exp (brownianGridMax B T w)
      ∂(μ.tilted (fun w ↦ -(centeredScaled B w T/2)))) = maxExpFormula (T:ℝ) := by
  let _ : IsProbabilityMeasure μ := hB.toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
  have hmZ : Measurable (fun w ↦ centeredScaled B w T) :=
    measurable_const.mul ((hmB T).sub (hmB 0))
  have hmM := measurable_brownianGridMax B hmB T
  have hC := hB.cont.mono (fun w hw ↦ brownianGridMax_spec B w hT hw)
  exact tilted_expectation_of_joint_reflection μ _ _ T hT hmZ hmM
    (hC.mono (fun _ hw ↦ hw.1)) (centeredScaled_law hB.toIsPreBrownianReal T).map_eq
    (brownian_jointEndpointReflection μ hB hmB T hT _ hmM
      (hC.mono (fun _ hw a _ ↦ hw.2 a)))
end CubeBrownian
