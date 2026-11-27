import BrownianExpectation
import Mathlib.MeasureTheory.Integral.Indicator
open MeasureTheory Set Filter
open scoped Topology
namespace CubeBrownian

theorem endpoint_reflection_CDF_limit {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (a z : ℝ)
    (E : ℕ → Set Ω) (hmE : ∀ n, MeasurableSet (E n)) (hinc : Monotone E)
    (Z : Ω → ℝ) (A : ℕ → Ω → ℝ) (hmZ : Measurable Z) (hmA : ∀ n, Measurable (A n))
    (hAtom : μ {w | Z w = 2*a-z} = 0)
    (hA : ∀ᵐ w ∂μ, w ∈ (⋃ n, E n) → Tendsto (fun n ↦ A n w) atTop (𝓝 a))
    (hR : ∀ n, μ (E n ∩ {w | Z w ≤ z}) = μ (E n ∩ {w | 2*A n w-Z w ≤ z})) :
    μ ((⋃ n, E n) ∩ {w | Z w ≤ z}) = μ ((⋃ n, E n) ∩ {w | 2*a-Z w ≤ z}) := by
  let F := fun n ↦ E n ∩ {w | Z w ≤ z}
  let G := fun n ↦ E n ∩ {w | 2*A n w-Z w ≤ z}
  let U := ⋃ n, E n
  let S := U ∩ {w | 2*a-Z w ≤ z}
  have hMF : Monotone F := fun i j hij ↦ Set.inter_subset_inter (hinc hij) (subset_refl _)
  have hUnion : (⋃ n, F n) = U ∩ {w | Z w ≤ z} := by simp only [F,U, iUnion_inter]
  have h₁ := tendsto_measure_iUnion_atTop (μ := μ) hMF
  have hNo : ∀ᵐ w ∂μ, 2*a-Z w ≠ z := by
    rw [ae_iff]
    have he : {w | ¬ 2*a-Z w ≠ z} = {w | Z w = 2*a-z} := by
      ext w
      simp only [Set.mem_setOf_eq,not_not]
      constructor <;> intro h <;> linarith only [h]
    rw [he,hAtom]
  have hFS : ∀ᵐ w ∂μ, ∀ᶠ n in atTop, w ∈ G n ↔ w ∈ S := by
    filter_upwards [hNo,hA] with w hNE hA'
    by_cases hw : w ∈ U
    · obtain ⟨k,hk⟩ := Set.mem_iUnion.mp hw
      have hE : ∀ᶠ n in atTop, w ∈ E n :=
        (eventually_ge_atTop k).mono (fun n hn ↦ hinc hn hk)
      have ht : Tendsto (fun n ↦ 2*A n w-Z w) atTop (𝓝 (2*a-Z w)) :=
        (tendsto_const_nhds.mul (hA' hw)).sub tendsto_const_nhds
      rcases lt_or_gt_of_ne hNE with hl | hg
      · have hL : ∀ᶠ n in atTop, 2*A n w-Z w < z := ht.eventually_lt_const hl
        filter_upwards [hE,hL] with n hnE hnL
        simp only [G,S,Set.mem_inter_iff,Set.mem_setOf_eq,hnE,hnL.le,hw,hl.le,and_self]
      · have hG : ∀ᶠ n in atTop, z < 2*A n w-Z w := ht.eventually_const_lt hg
        filter_upwards [hE,hG] with n hnE hnG
        simp only [G,S,Set.mem_inter_iff,Set.mem_setOf_eq,hnE,not_le_of_gt hnG,
          hw,not_le_of_gt hg,and_false]
    · exact Eventually.of_forall fun n ↦ by
        have hnE : w ∉ E n := fun hn ↦ hw (Set.mem_iUnion.mpr ⟨n,hn⟩)
        simp only [G,S,Set.mem_inter_iff,hnE,hw,false_and]
  have hmG (n : ℕ) : MeasurableSet (G n) :=
    (hmE n).inter (measurableSet_le ((measurable_const.mul (hmA n)).sub hmZ) measurable_const)
  have hmS : MeasurableSet S :=
    (MeasurableSet.iUnion hmE).inter (measurableSet_le (measurable_const.sub hmZ) measurable_const)
  have h₂ := tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure atTop hmS hmG hFS
  rw [hUnion] at h₁
  exact tendsto_nhds_unique (h₁.congr hR) h₂
end CubeBrownian
#print axioms CubeBrownian.endpoint_reflection_CDF_limit
