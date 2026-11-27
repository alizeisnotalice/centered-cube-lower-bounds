import DyadicFirstCross
import ReflectionLimit
import ReflectionDecomposition

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology
namespace CubeBrownian

noncomputable def centeredScaled {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (w : Ω) (t : ℝ≥0) : ℝ := Real.sqrt 2 * (B t w-B 0 w)

theorem centeredScaled_zero {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (w : Ω) :
    centeredScaled B w 0 = 0 := by simp [centeredScaled]

theorem centeredScaled_law {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) (T : ℝ≥0) :
    HasLaw (fun w ↦ centeredScaled B w T) (gaussianReal 0 (2*T)) μ := by
  have hs : NNReal.mk ((Real.sqrt 2)^2) (sq_nonneg _) = 2 := by
    apply NNReal.eq
    exact Real.sq_sqrt (by norm_num)
  have hd : nndist (T:ℝ) ((0:ℝ≥0):ℝ) = T := by
    apply NNReal.eq
    simp
  have h := gaussianReal_const_mul (hB.hasLaw_sub T 0) (Real.sqrt 2)
  change HasLaw (fun w ↦ centeredScaled B w T)
    (gaussianReal (Real.sqrt 2*0) (NNReal.mk ((Real.sqrt 2)^2) (sq_nonneg _) *
      nndist (T:ℝ) ((0:ℝ≥0):ℝ))) μ at h
  rwa [mul_zero,hs,hd] at h

theorem brownian_jointEndpointReflection {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B μ)
    (hmB : ∀ t, Measurable (B t)) (T : ℝ≥0) (hT : 0 < T)
    (M : Ω → ℝ) (_hmM : Measurable M)
    (hM : ∀ᵐ w ∂μ, ∀ a : ℝ, 0 ≤ a →
      (a < M w ↔ ∃ t ≤ T, a < centeredScaled B w t)) :
    JointEndpointReflection μ (fun w ↦ centeredScaled B w T) M T := by
  let f := centeredScaled B
  let Z := fun w ↦ f w T
  have hμ : IsProbabilityMeasure μ := hB.toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
  let := hμ
  have hZLaw := centeredScaled_law hB.toIsPreBrownianReal T
  have hfm (t : ℝ≥0) : Measurable (fun w ↦ f w t) :=
    measurable_const.mul ((hmB t).sub (hmB 0))
  have hmZ : Measurable Z := hfm T
  have hAtom (y : ℝ) : μ (Z ⁻¹' {y}) = 0 := by
    have hNo : (gaussianReal 0 (2*T)) {y} = 0 :=
      gaussianReal_absolutelyContinuous 0 (by positivity) (measure_singleton y)
    rw [← hZLaw.map_eq, Measure.map_apply hmZ (measurableSet_singleton y)] at hNo
    exact hNo
  intro a ha
  let E (r : ℕ) : Set Ω := {w | dyadicHits T r a (f w)}
  let A (r : ℕ) (w : Ω) := firstCrossValue a (dyadicIncrements T r (f w))
  have hE (r : ℕ) : MeasurableSet (E r) := by
    have he : E r = ⋃ k : ℕ, {w | k ≤ 2^r ∧ a < f w (dyadicT T r k)} := by
      ext w
      simp [E,dyadicHits]
    rw [he]
    apply MeasurableSet.iUnion
    intro k
    by_cases hk : k ≤ 2^r
    · simpa only [hk,true_and] using
        (measurableSet_lt measurable_const (hfm (dyadicT T r k)) :
          MeasurableSet {w | a < f w (dyadicT T r k)})
    · simp [hk]
  have hA (r : ℕ) : Measurable (A r) := by
    apply (measurable_firstCrossValue a).comp
    exact measurable_pi_iff.mpr (fun i ↦ (hfm _).sub (hfm _))
  have hEm : Monotone E := fun _ _ hj w hw ↦ dyadicHits_mono T a (f w) hj hw
  have hC : ∀ᵐ w ∂μ, Continuous (f w) := hB.cont.mono (fun w hw ↦
    continuous_const.mul (hw.sub continuous_const))
  have hLim : ∀ᵐ w ∂μ, w ∈ (⋃ r, E r) →
      Tendsto (fun r ↦ A r w) atTop (𝓝 a) := hC.mono (fun w hw h ↦
    dyadicOvershoot_tendsto a ha (f w) (centeredScaled_zero B w) hw (mem_iUnion.mp h))
  have hAER : (⋃ r, E r) =ᵐ[μ] {w | a < M w} := by
    filter_upwards [hC,hM] with w hCw hMw
    simpa only [E,mem_iUnion,mem_ofPred_eq] using
      (dyadicHits_iff_exists hT a (f w) hCw).trans (hMw a ha).symm
  have hSub : Z ⁻¹' Ioi a ⊆ ⋃ r, E r := by
    intro w hw
    change a < f w T at hw
    exact mem_iUnion.mpr ⟨0,2^0,le_rfl,by simpa only [dyadicT_last] using hw⟩
  have hFin (r : ℕ) (z : ℝ) :
      μ (E r ∩ {w | Z w ≤ z}) = μ (E r ∩ {w | 2*A r w-Z w ≤ z}) := by
    let t : Fin (2^r+1) → ℝ≥0 := fun i ↦ dyadicT T r i
    have ht : Monotone t := fun _ _ hij ↦ dyadicT_mono T r hij
    have H := brownian_grid_CDF hB.toIsPreBrownianReal (Real.sqrt 2) t ht a z
    let D (w : Ω) : Fin (2^r) → ℝ := fun i ↦ Real.sqrt 2 * (B (t i.succ) w-B (t i.castSucc) w)
    have hD : D = fun w ↦ dyadicIncrements T r (f w) := by
      funext w i
      change Real.sqrt 2 * (B (dyadicT T r ((i:ℕ)+1)) w-B (dyadicT T r i) w) =
        Real.sqrt 2 * (B (dyadicT T r ((i:ℕ)+1)) w-B 0 w) -
        Real.sqrt 2 * (B (dyadicT T r i) w-B 0 w)
      ring
    have hTotal (w : Ω) : (∑ i, D w i) = Z w := by
      rw [hD]
      change (∑ (i : Fin (2^r)), (((f w) ∘ dyadicT T r) ((i:ℕ)+1) -
        ((f w) ∘ dyadicT T r) i)) = Z w
      rw [total_pathDifferences]
      simp [dyadicT_last,dyadicT_zero,Z,f,centeredScaled_zero]
    have hHit : {w | ∃ k, a < partialSum k (D w)} = E r := by
      rw [hD]
      ext w
      change (∃ k, a < partialSum k (dyadicIncrements T r (f w))) ↔ dyadicHits T r a (f w)
      exact (dyadicHits_iff_prefix T r a ha (f w) (centeredScaled_zero B w)).symm
    change μ ({w | ∃ k, a < partialSum k (D w)} ∩ {w | (∑ i, D w i) ≤ z}) =
      μ ({w | ∃ k, a < partialSum k (D w)} ∩ {w | 2*firstCrossValue a (D w) - (∑ i, D w i) ≤ z}) at H
    simp only [hHit,hTotal] at H
    change μ (E r ∩ {w | Z w ≤ z}) = μ (E r ∩ {w | 2*firstCrossValue a (D w)-Z w ≤ z}) at H
    rwa [hD] at H
  have hSym (z : ℝ) : μ ((⋃ r,E r) ∩ Z ⁻¹' Iic z) =
      μ ((⋃ r,E r) ∩ (fun w ↦ 2*a-Z w) ⁻¹' Iic z) :=
    endpoint_reflection_CDF_limit μ a z E hE hEm Z A hmZ hA (hAtom (2*a-z)) hLim (fun r ↦ hFin r z)
  have h := reflect_endpoint_decompose μ (⋃ r, E r) Z a
    (MeasurableSet.iUnion hE) hmZ hSub (hAtom a) hSym
  rw [Measure.restrict_congr_set hAER, hZLaw.map_eq] at h
  exact h
end CubeBrownian
#print axioms CubeBrownian.brownian_jointEndpointReflection
