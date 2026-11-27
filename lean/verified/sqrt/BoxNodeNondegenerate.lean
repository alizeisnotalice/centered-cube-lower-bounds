import BoxNodeApproximation
import Mathlib.MeasureTheory.Measure.OpenPos

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology RealInnerProductSpace
namespace CubeBrownian

lemma continuous_centeredBoxNode (e t : ℝ) : Continuous (centeredBoxNode e t) := by
  unfold centeredBoxNode boxNode boxRamp
  fun_prop

theorem centeredBoxNodeL2_ne_of_separated {e s t : ℝ} (he : 0 < e)
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s+e ≤ t) :
    centeredBoxNodeL2 e s he hs ≠ centeredBoxNodeL2 e t he ht := by
  intro h
  have hs' : (centeredBoxNodeL2 e s he hs : ℝ → ℝ) =ᵐ[volume] centeredBoxNode e s :=
    MemLp.coeFn_toLp _
  have ht' : (centeredBoxNodeL2 e t he ht : ℝ → ℝ) =ᵐ[volume] centeredBoxNode e t :=
    MemLp.coeFn_toLp _
  rw [h] at hs'
  have hEq := (Continuous.ae_eq_iff_eq (μ:=(volume : Measure ℝ))
    (continuous_centeredBoxNode e s) (continuous_centeredBoxNode e t)).mp (hs'.symm.trans ht')
  let x := s+e/2
  have hRamp1 : e ≤ x+e/2-s := by dsimp [x]; ring_nf; exact le_rfl
  have hRamp0 : x+e/2-t ≤ 0 := by dsimp [x]; linarith only [hst]
  have hx := congrFun hEq x
  rw [centeredBoxNode,centeredBoxNode,boxNode,boxNode,boxRamp_one he hRamp1,
    boxRamp_zero he hRamp0] at hx
  linarith only [hx]

lemma boxRamp_three_quarters_le {e x : ℝ} (he : 0 < e) (hx : 3*e/4 ≤ x) :
    3/4 ≤ boxRamp e x := by
  apply le_min (by norm_num)
  exact le_max_of_le_right ((le_div_iff₀ he).2 (by convert hx using 1 <;> ring))

lemma boxRamp_le_quarter {e x : ℝ} (he : 0 < e) (hx : x ≤ e/4) :
    boxRamp e x ≤ 1/4 := by
  exact (min_le_right _ _).trans (max_le (by norm_num) ((div_le_iff₀ he).2 (by
    convert hx using 1 <;> ring)))

theorem centeredBoxNodeL2_sq_ge_of_separated {e s t : ℝ} (he : 0 < e)
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s+e ≤ t) :
    (t-s)/8 ≤ ‖centeredBoxNodeL2 e s he hs-centeredBoxNodeL2 e t he ht‖^2 := by
  let C := Icc (s+e/4) (t-e/4)
  let H : ℝ → ℝ := C.indicator (fun _ ↦ (1:ℝ)/4)
  let f := centeredBoxNode e s
  let g := centeredBoxNode e t
  let U := centeredBoxNodeL2 e s he hs - centeredBoxNodeL2 e t he ht
  have hs' : (centeredBoxNodeL2 e s he hs : ℝ → ℝ) =ᵐ[volume] f := MemLp.coeFn_toLp _
  have ht' : (centeredBoxNodeL2 e t he ht : ℝ → ℝ) =ᵐ[volume] g := MemLp.coeFn_toLp _
  have hU : (U : ℝ → ℝ) =ᵐ[volume] fun x ↦ f x-g x := by
    filter_upwards [Lp.coeFn_sub (centeredBoxNodeL2 e s he hs) (centeredBoxNodeL2 e t he ht),hs',ht']
      with x hx hf hg
    simpa only [U,Pi.sub_apply,hf,hg] using hx
  have hQ : ‖U‖^2 = ∫ x, (f x-g x)^2 := by
    rw [← real_inner_self_eq_norm_sq,MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hU] with x hx
    rw [hx,real_inner_self_eq_norm_sq,Real.norm_eq_abs,sq_abs]
  have hI : Integrable (fun x ↦ (f x-g x)^2) volume :=
    (memLp_two_iff_integrable_sq ((memLp_centeredBoxNode he hs).sub
      (memLp_centeredBoxNode he ht)).aestronglyMeasurable).1
        ((memLp_centeredBoxNode he hs).sub (memLp_centeredBoxNode he ht))
  have hPt (x : ℝ) : H x ≤ (f x-g x)^2 := by
    rcases em (x ∈ C) with hx|hx
    · have hL : 3*e/4 ≤ x+e/2-s := by linarith only [hx.1]
      have hR : x+e/2-t ≤ e/4 := by linarith only [hx.2]
      have h1 := boxRamp_three_quarters_le he hL
      have h2 := boxRamp_le_quarter he hR
      change C.indicator (fun _ ↦ (1:ℝ)/4) x ≤ _
      rw [indicator_of_mem hx]
      dsimp only [f,g,centeredBoxNode,boxNode]
      nlinarith only [h1,h2,
        sq_nonneg (boxRamp e (x+e/2-s)-boxRamp e (x+e/2-t)-1/2)]
    · simp [H,hx,sq_nonneg]
  have hJ : (∫ x, H x) = (t-s-e/2)/4 := by
    have hC : MeasurableSet C := measurableSet_Icc
    unfold H
    rw [integral_indicator hC,integral_const]
    have hOrd : s+e/4 ≤ t-e/4 := by linarith only [he,hst]
    change (((volume : Measure ℝ).restrict C).real univ) • (1/4:ℝ) = _
    rw [Measure.real,Measure.restrict_apply MeasurableSet.univ,univ_inter]
    change (volume.real C) • (1/4:ℝ) = _
    rw [Real.volume_real_Icc_of_le hOrd,smul_eq_mul]
    ring
  have hHi : ∫ x, H x ≤ ∫ x, (f x-g x)^2 :=
    integral_mono_of_nonneg (Eventually.of_forall fun x ↦ by
      by_cases hx : x ∈ C <;> simp [H,hx] <;> norm_num) hI (Eventually.of_forall hPt)
  rw [hJ] at hHi
  change (t-s)/8 ≤ ‖U‖^2
  rw [hQ]
  linarith only [hHi,hst]

end CubeBrownian
#print axioms CubeBrownian.centeredBoxNodeL2_ne_of_separated
#print axioms CubeBrownian.centeredBoxNodeL2_sq_ge_of_separated
