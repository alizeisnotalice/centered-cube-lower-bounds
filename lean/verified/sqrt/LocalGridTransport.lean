import GridAnchorTilt
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
namespace CubeBrownian

theorem absolute_cell_tail_eq_of_dyadic {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) (ν : Measure Ξ) (F : Ω → ℝ≥0 → ℝ) (G : Ξ → ℝ≥0 → ℝ)
    (hmF : ∀ t, Measurable (F · t)) (hmG : ∀ t, Measurable (G · t))
    (hFc : ∀ᵐ w ∂μ, Continuous (F w)) (hGc : ∀ᵐ w ∂ν, Continuous (G w))
    (hF0 : ∀ w, F w 0 = 0) (hG0 : ∀ w, G w 0 = 0)
    (A : ℝ≥0) (hA : 0 < A)
    (hLaw : ∀ r, μ.map (fun w ↦ dyadicIncrements A r (F w)) =
      ν.map (fun w ↦ dyadicIncrements A r (G w)))
    (x : ℝ) (hx : 0 ≤ x) :
    μ {w | ∃ t ≤ A, x < |F w t|} = ν {w | ∃ t ≤ A, x < |G w t|} := by
  let EF (r : ℕ) : Set Ω := {w | dyadicHits A r x (fun t ↦ |F w t|)}
  let EG (r : ℕ) : Set Ξ := {w | dyadicHits A r x (fun t ↦ |G w t|)}
  have hEF : Monotone EF := fun _ _ h w hw ↦ dyadicHits_mono A x (fun t ↦ |F w t|) h hw
  have hEG : Monotone EG := fun _ _ h w hw ↦ dyadicHits_mono A x (fun t ↦ |G w t|) h hw
  have hFae : (⋃ r, EF r) =ᵐ[μ] {w | ∃ t ≤ A, x < |F w t|} := by
    filter_upwards [hFc] with w hw
    simpa only [EF,mem_iUnion,mem_ofPred_eq] using dyadicHits_iff_exists hA x _ hw.abs
  have hGae : (⋃ r, EG r) =ᵐ[ν] {w | ∃ t ≤ A, x < |G w t|} := by
    filter_upwards [hGc] with w hw
    simpa only [EG,mem_iUnion,mem_ofPred_eq] using dyadicHits_iff_exists hA x _ hw.abs
  rw [← measure_congr hFae,← measure_congr hGae]
  have hE (r : ℕ) : μ (EF r) = ν (EG r) := by
    let P : Set (Fin (2^r) → ℝ) := {y | ∃ k, x < |partialSum k y|}
    have hmP : MeasurableSet P := by
      have he : P = ⋃ k : ℕ, {y | x < |partialSum k y|} := by ext y; simp [P]
      rw [he]
      exact .iUnion (fun k ↦ measurableSet_lt measurable_const (measurable_partialSum k).abs)
    let DF w := dyadicIncrements A r (F w)
    let DG w := dyadicIncrements A r (G w)
    have hmDF : Measurable DF := measurable_pi_iff.mpr (fun i ↦ (hmF _).sub (hmF _))
    have hmDG : Measurable DG := measurable_pi_iff.mpr (fun i ↦ (hmG _).sub (hmG _))
    have hTrans (f : ℝ≥0 → ℝ) (h0 : f 0 = 0) :
        dyadicHits A r x (fun t ↦ |f t|) ↔ ∃ k, x < |partialSum k (dyadicIncrements A r f)| := by
      have hTel (k : ℕ) : partialSum k (dyadicIncrements A r f) =
          f (dyadicT A r (min (k+1) (2^r))) := by
        change partialSum k (fun (i : Fin (2^r)) ↦ (f ∘ dyadicT A r) ((i:ℕ)+1) - (f ∘ dyadicT A r) i) = _
        rw [partialSum_pathDifferences]
        simp [dyadicT_zero,h0]
      simp only [dyadicHits,hTel]
      constructor
      · rintro ⟨k,hk,h⟩
        cases k with
        | zero => simp [dyadicT_zero,h0,not_lt_of_ge hx] at h
        | succ j => exact ⟨j,by simpa only [min_eq_left hk] using h⟩
      · rintro ⟨k,h⟩
        exact ⟨_,min_le_right ..,h⟩
    have heF : EF r = DF ⁻¹' P := by ext w; exact hTrans (F w) (hF0 w)
    have heG : EG r = DG ⁻¹' P := by ext w; exact hTrans (G w) (hG0 w)
    rw [heF,heG,← Measure.map_apply hmDF hmP,← Measure.map_apply hmDG hmP]
    exact congrArg (fun m : Measure (Fin (2^r) → ℝ) ↦ m P) (hLaw r)
  have hL := tendsto_measure_iUnion_atTop (μ:=μ) hEF
  have hR := tendsto_measure_iUnion_atTop (μ:=ν) hEG
  exact tendsto_nhds_unique (hL.congr hE) hR
end CubeBrownian
#print axioms CubeBrownian.absolute_cell_tail_eq_of_dyadic
