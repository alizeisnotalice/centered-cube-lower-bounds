import AnchorCellLaw
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
namespace CubeBrownian

theorem anchorCell_absolute_tail_eq {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B μ)
    (hmB : ∀ t, Measurable (B t)) (anchor left A : ℝ≥0) (hA : 0 < A)
    (hPos : anchor ≤ left ∨ left+A ≤ anchor) (x : ℝ) (hx : 0 ≤ x) :
    (anchorTiltedMeasure μ B (Real.sqrt 2) 1 anchor)
      {w | ∃ s ≤ A, x < |anchorCellCentered B (Real.sqrt 2) 1 anchor left w s|} =
    μ {w | ∃ s ≤ A, x < |centeredScaled B w s|} := by
  let Q := anchorTiltedMeasure μ B (Real.sqrt 2) 1 anchor
  let f := anchorCellCentered B (Real.sqrt 2) 1 anchor left
  let g := centeredScaled B
  have hAC : Q ≪ μ := tilted_absolutelyContinuous _ _
  have hFM (t : ℝ≥0) : Measurable (f · t) :=
    (measurable_const.mul ((hmB (left+t)).sub (hmB left))).sub measurable_const
  have hGM (t : ℝ≥0) : Measurable (g · t) :=
    measurable_const.mul ((hmB t).sub (hmB 0))
  have hFC : ∀ᵐ w ∂Q, Continuous (f w) := hAC.ae_le (hB.cont.mono (fun w h ↦ by
    change Continuous (fun s : ℝ≥0 ↦ Real.sqrt 2*(B (left+s) w-B left w) -
      anchorDrift (Real.sqrt 2) 1 anchor left*(s:ℝ))
    fun_prop))
  have hGC : ∀ᵐ w ∂μ, Continuous (g w) :=
    hB.cont.mono (fun w h ↦ continuous_const.mul (h.sub continuous_const))
  apply absolute_cell_tail_eq_of_dyadic Q μ f g hFM hGM hFC hGC
    (fun w ↦ by simp [f,anchorCellCentered]) (centeredScaled_zero B) A hA _ x hx
  intro r
  have H := anchorCell_dyadic_centered_law μ hB.toIsPreBrownianReal hmB (Real.sqrt 2) 1 anchor left A hPos r
  dsimp only at H
  have hh : NNReal.mk ((Real.sqrt 2)^2) (sq_nonneg _) = 2 := by
    apply NNReal.eq
    exact Real.sq_sqrt (by norm_num)
  rw [hh] at H
  exact H.trans (dyadicIncrements_centered_law μ hB.toIsPreBrownianReal A r).symm

theorem anchorCell_drifted_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B μ)
    (hmB : ∀ t, Measurable (B t)) (anchor left A : ℝ≥0) (hA : 0 < A)
    (hPos : anchor ≤ left ∨ left+A ≤ anchor) (b x : ℝ)
    (hb : (A:ℝ) ≤ b) (hx : b < x) :
    (anchorTiltedMeasure μ B (Real.sqrt 2) 1 anchor)
      {w | ∃ s ≤ A, x < |driftedCentered B w (left+s) - driftedCentered B w left|} ≤
    4 * ENNReal.ofReal (Real.exp (-((x-b)^2)/(4*b))) := by
  let Q := anchorTiltedMeasure μ B (Real.sqrt 2) 1 anchor
  let f := anchorCellCentered B (Real.sqrt 2) 1 anchor left
  let m := anchorDrift (Real.sqrt 2) 1 anchor left
  have hAR : 0 < (A:ℝ) := by exact_mod_cast hA
  have hbpos : 0 < b := hAR.trans_le hb
  have hm : |m-1| = 1 := by
    unfold m anchorDrift
    split
    · norm_num
    · rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
      norm_num
  have hsub : {w | ∃ s ≤ A, x < |driftedCentered B w (left+s) - driftedCentered B w left|} ⊆
      {w | ∃ s ≤ A, x-b < |f w s|} := by
    rintro w ⟨s,hs,h⟩
    refine ⟨s,hs,?_⟩
    have he : driftedCentered B w (left+s) - driftedCentered B w left =
      f w s+(m-1)*(s:ℝ) := by
      unfold driftedCentered centeredScaled f anchorCellCentered
      push_cast
      ring
    have hu : |f w s+(m-1)*(s:ℝ)| ≤ |f w s| + (s:ℝ) := by
      apply (abs_add_le _ _).trans_eq
      rw [abs_mul,hm,one_mul,abs_of_nonneg (NNReal.coe_nonneg s)]
    have hs' : (s:ℝ) ≤ b := (show (s:ℝ) ≤ (A:ℝ) from by exact_mod_cast hs).trans hb
    rw [he] at h
    linarith only [h,hu,hs']
  calc
    Q _ ≤ Q {w | ∃ s ≤ A, x-b < |f w s|} := measure_mono hsub
    _ = μ {w | ∃ s ≤ A, x-b < |centeredScaled B w s|} :=
      anchorCell_absolute_tail_eq μ hB hmB anchor left A hA hPos (x-b) (sub_nonneg.mpr hx.le)
    _ ≤ 4 * ENNReal.ofReal (Real.exp (-((x-b)^2)/(4*(A:ℝ)))) :=
      brownian_absolute_max_bound μ hB hmB A hA (x-b) (sub_nonneg.mpr hx.le)
    _ ≤ _ := by
      apply mul_le_mul' (le_refl _)
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      simp only [neg_div]
      apply neg_le_neg
      exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by gcongr)
end CubeBrownian
#print axioms CubeBrownian.anchorCell_drifted_bound
