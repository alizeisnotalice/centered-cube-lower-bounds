import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology RealInnerProductSpace
namespace CubeBrownian

noncomputable def boxRamp (e x : ℝ) : ℝ := min 1 (max 0 (x/e))
noncomputable def boxNode (e t x : ℝ) : ℝ := boxRamp e x-boxRamp e (x-t)
noncomputable def stepNode (t : ℝ) : ℝ → ℝ := (Icc 0 t).indicator (fun _ ↦ 1)

theorem boxRamp_zero {e x : ℝ} (he : 0 < e) (hx : x ≤ 0) :
    boxRamp e x = 0 := by
  unfold boxRamp
  rw [max_eq_left (div_nonpos_of_nonpos_of_nonneg hx he.le)]
  norm_num

theorem boxRamp_one {e x : ℝ} (he : 0 < e) (hx : e ≤ x) :
    boxRamp e x = 1 := by
  unfold boxRamp
  exact min_eq_left (le_max_of_le_right ((le_div_iff₀ he).2 (by simpa using hx)))

theorem boxNode_bounds {e t : ℝ} (he : 0 < e) (ht : 0 ≤ t) (x : ℝ) :
    0 ≤ boxNode e t x ∧ boxNode e t x ≤ 1 := by
  unfold boxNode
  have hm : Monotone (boxRamp e) := by
    intro a b hab
    unfold boxRamp
    gcongr
  have ha (z : ℝ) : 0 ≤ boxRamp e z ∧ boxRamp e z ≤ 1 := by
    unfold boxRamp
    exact ⟨le_min zero_le_one (le_max_left ..),min_le_left ..⟩
  exact ⟨sub_nonneg.mpr (hm (by linarith)),(sub_le_self _ (ha (x-t)).1).trans (ha x).2⟩

theorem boxNode_outside_support {e t x : ℝ} (he : 0 < e) (ht : 0 ≤ t)
    (hx : x ∉ Icc 0 (t+e)) : boxNode e t x = 0 := by
  unfold boxNode
  by_cases hL : x < 0
  · rw [boxRamp_zero he hL.le,boxRamp_zero he (by linarith)]
    ring
  · have hR : t+e < x := by
      by_contra! h
      exact hx ⟨le_of_not_gt hL,h⟩
    rw [boxRamp_one he (by linarith),boxRamp_one he (by linarith)]
    ring

theorem boxNode_off_endpoints {e t x : ℝ} (he : 0 < e) (ht : 0 ≤ t)
    (h₀ : x ∉ Icc 0 e) (h₁ : x ∉ Icc t (t+e)) : boxNode e t x = stepNode t x := by
  by_cases hneg : x < 0
  · have hout : x ∉ Icc 0 (t+e) := fun h ↦ (not_le_of_gt hneg) h.1
    rw [boxNode_outside_support he ht hout]
    exact (indicator_of_notMem (fun h : x ∈ Icc 0 t ↦ (not_le_of_gt hneg) h.1) _).symm
  · have hx : 0 ≤ x := le_of_not_gt hneg
    have hxe : e < x := lt_of_not_ge (fun h ↦ h₀ ⟨hx,h⟩)
    by_cases hxt : x ≤ t
    · rw [stepNode,indicator_of_mem (show x ∈ Icc 0 t from ⟨hx,hxt⟩),boxNode,boxRamp_one he hxe.le,
        boxRamp_zero he (sub_nonpos.mpr hxt),sub_zero]
    · have hxo : x ∉ Icc 0 (t+e) := fun h ↦ h₁ ⟨(lt_of_not_ge hxt).le,h.2⟩
      rw [boxNode_outside_support he ht hxo]
      exact (indicator_of_notMem (fun h : x ∈ Icc 0 t ↦ hxt h.2) _).symm

theorem boxNode_sq_error_le_indicators {e t : ℝ} (he : 0 < e) (ht : 0 ≤ t) (x : ℝ) :
    (boxNode e t x-stepNode t x)^2 ≤
      (Icc 0 e).indicator (fun _ ↦ (1:ℝ)) x + (Icc t (t+e)).indicator (fun _ ↦ (1:ℝ)) x := by
  have hstep : 0 ≤ stepNode t x ∧ stepNode t x ≤ 1 := by
    unfold stepNode
    by_cases hx : x ∈ Icc 0 t <;> simp [hx]
  have hb := boxNode_bounds he ht x
  have hsq : (boxNode e t x-stepNode t x)^2 ≤ 1 := by
    have h := abs_le.mpr ⟨show -1 ≤ boxNode e t x-stepNode t x by linarith only [hb.1,hstep.2],
      show boxNode e t x-stepNode t x ≤ 1 by linarith only [hb.2,hstep.1]⟩
    simpa only [sq_abs,one_pow] using pow_le_pow_left₀ (abs_nonneg _) h 2
  by_cases h₀ : x ∈ Icc 0 e <;> by_cases h₁ : x ∈ Icc t (t+e)
  · simp only [indicator_of_mem h₀,indicator_of_mem h₁]
    linarith
  · simpa only [indicator_of_mem h₀,indicator_of_notMem h₁,add_zero] using hsq
  · simpa only [indicator_of_notMem h₀,indicator_of_mem h₁,zero_add] using hsq
  · simp [boxNode_off_endpoints he ht h₀ h₁,h₀,h₁]

lemma interval_one_memLp (a b : ℝ) (p : ℝ≥0∞) :
    MemLp ((Icc a b).indicator (fun _ ↦ (1:ℝ))) p volume :=
  memLp_indicator_const p measurableSet_Icc.nullMeasurableSet 1 (.inr measure_Icc_lt_top.ne)

theorem memLp_boxNode {e t : ℝ} (he : 0 < e) (ht : 0 ≤ t) :
    MemLp (boxNode e t) 2 volume := by
  have hm : Measurable (boxNode e t) := by unfold boxNode boxRamp; fun_prop
  apply (interval_one_memLp 0 (t+e) 2).mono' hm.aestronglyMeasurable
  exact Eventually.of_forall fun x ↦ by
    by_cases hx : x ∈ Icc 0 (t+e)
    · rw [indicator_of_mem hx,Real.norm_eq_abs,abs_of_nonneg (boxNode_bounds he ht x).1]
      exact (boxNode_bounds he ht x).2
    · rw [indicator_of_notMem hx,boxNode_outside_support he ht hx,norm_zero]

noncomputable def boxNodeL2 (e t : ℝ) (he : 0 < e) (ht : 0 ≤ t) : Lp ℝ 2 (volume : Measure ℝ) :=
  (memLp_boxNode he ht).toLp (boxNode e t)

noncomputable def stepNodeL2 (t : ℝ) : Lp ℝ 2 (volume : Measure ℝ) :=
  (interval_one_memLp 0 t 2).toLp (stepNode t)

theorem boxNode_L2_error {e t : ℝ} (he : 0 < e) (ht : 0 ≤ t) :
    ‖boxNodeL2 e t he ht-stepNodeL2 t‖^2 ≤ 2*e := by
  let f := boxNode e t
  let g := stepNode t
  let L := boxNodeL2 e t he ht-stepNodeL2 t
  have hL : (L : ℝ → ℝ) =ᵐ[volume] fun x ↦ f x-g x := by
    have hstepAE : (stepNodeL2 t : ℝ → ℝ) =ᵐ[volume] stepNode t :=
      MemLp.coeFn_toLp (f := stepNode t) (interval_one_memLp 0 t 2)
    filter_upwards [Lp.coeFn_sub (boxNodeL2 e t he ht) (stepNodeL2 t),
      (MemLp.coeFn_toLp (memLp_boxNode he ht)),
      hstepAE] with x hsub hbox hstep
    rw [Pi.sub_apply,show boxNodeL2 e t he ht x = f x from hbox,hstep] at hsub
    exact hsub
  have hinner : ‖L‖^2 = ∫ x, (f x-g x)^2 := by
    rw [← real_inner_self_eq_norm_sq,MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hL] with x hx
    rw [hx,real_inner_self_eq_norm_sq,Real.norm_eq_abs,sq_abs]
  have hInt (a b : ℝ) : Integrable ((Icc a b).indicator (fun _ ↦ (1:ℝ))) volume :=
    (memLp_one_iff_integrable).mp (interval_one_memLp a b 1)
  rw [show ‖boxNodeL2 e t he ht-stepNodeL2 t‖^2 = ‖L‖^2 by rfl,hinner]
  calc
    _ ≤ ∫ x, (Icc 0 e).indicator (fun _ ↦ (1:ℝ)) x + (Icc t (t+e)).indicator (fun _ ↦ (1:ℝ)) x :=
      integral_mono_of_nonneg (Eventually.of_forall fun _ ↦ sq_nonneg _)
        ((hInt 0 e).add (hInt t (t+e))) (Eventually.of_forall (boxNode_sq_error_le_indicators he ht))
    _ = 2*e := by
      rw [integral_add (hInt 0 e) (hInt t (t+e)),
        integral_indicator measurableSet_Icc,integral_indicator measurableSet_Icc]
      simp only [integral_const,Measure.real,Measure.restrict_apply MeasurableSet.univ,univ_inter,
        Real.volume_Icc,smul_eq_mul,mul_one,sub_zero,add_sub_cancel_left,ENNReal.toReal_ofReal he.le]
      ring
/-- Actual centered-box ramp (not the one-sided translate) used in the paper. -/
noncomputable def centeredBoxNode (e t x : ℝ) : ℝ := boxNode e t (x+e/2)

lemma centeredBoxNode_off_endpoints {e t x : ℝ} (he : 0 < e) (ht : 0 ≤ t)
    (h₀ : x ∉ Icc (-e/2) (e/2)) (h₁ : x ∉ Icc (t-e/2) (t+e/2)) :
    centeredBoxNode e t x = stepNode t x := by
  have h0' : x+e/2 ∉ Icc 0 e := fun h ↦ h₀ ⟨by linarith only [h.1], by linarith only [h.2]⟩
  have h1' : x+e/2 ∉ Icc t (t+e) := fun h ↦ h₁ ⟨by linarith only [h.1],by linarith only [h.2]⟩
  rw [centeredBoxNode,boxNode_off_endpoints he ht h0' h1']
  unfold stepNode
  by_cases hx : x ∈ Icc 0 t
  · have ha : x < t-e/2 ∨ t+e/2 < x := by
      by_contra! H
      exact h₁ ⟨H.1,H.2⟩
    have hx' : x+e/2 ∈ Icc 0 t := ⟨by linarith only [hx.1,he],by
      rcases ha with ha|ha <;> linarith only [hx.2,he,ha]⟩
    simp only [indicator_of_mem hx,indicator_of_mem hx']
  · have hx' : x+e/2 ∉ Icc 0 t := by
      intro H
      apply hx
      refine ⟨?_,by linarith only [H.2,he]⟩
      by_contra! hz
      exact h₀ ⟨by linarith only [H.1],by linarith only [hz,he]⟩
    simp only [indicator_of_notMem hx,indicator_of_notMem hx']

lemma centeredBoxNode_sq_error_le_indicators {e t : ℝ} (he : 0 < e) (ht : 0 ≤ t) (x : ℝ) :
    (centeredBoxNode e t x-stepNode t x)^2 ≤
      (Icc (-e/2) (e/2)).indicator (fun _ ↦ (1:ℝ)) x +
        (Icc (t-e/2) (t+e/2)).indicator (fun _ ↦ (1:ℝ)) x := by
  have hstep : 0 ≤ stepNode t x ∧ stepNode t x ≤ 1 := by
    unfold stepNode
    by_cases hx : x ∈ Icc 0 t <;> simp [hx]
  have hb : 0 ≤ centeredBoxNode e t x ∧ centeredBoxNode e t x ≤ 1 :=
    boxNode_bounds he ht _
  have hsq : (centeredBoxNode e t x-stepNode t x)^2 ≤ 1 := by
    have h := abs_le.mpr ⟨show -1 ≤ centeredBoxNode e t x-stepNode t x by linarith only [hb.1,hstep.2],
      show centeredBoxNode e t x-stepNode t x ≤ 1 by linarith only [hb.2,hstep.1]⟩
    simpa only [sq_abs,one_pow] using pow_le_pow_left₀ (abs_nonneg _) h 2
  by_cases h₀ : x ∈ Icc (-e/2) (e/2) <;> by_cases h₁ : x ∈ Icc (t-e/2) (t+e/2)
  · simp only [indicator_of_mem h₀,indicator_of_mem h₁]
    linarith
  · simpa only [indicator_of_mem h₀,indicator_of_notMem h₁,add_zero] using hsq
  · simpa only [indicator_of_notMem h₀,indicator_of_mem h₁,zero_add] using hsq
  · simp [centeredBoxNode_off_endpoints he ht h₀ h₁,h₀,h₁]

lemma memLp_centeredBoxNode {e t : ℝ} (he : 0 < e) (ht : 0 ≤ t) :
    MemLp (centeredBoxNode e t) 2 volume := by
  have hm : Measurable (centeredBoxNode e t) := by
    unfold centeredBoxNode boxNode boxRamp
    fun_prop
  apply (interval_one_memLp (-e/2) (t+e/2) 2).mono' hm.aestronglyMeasurable
  exact Eventually.of_forall fun x ↦ by
    by_cases hx : x ∈ Icc (-e/2) (t+e/2)
    · have H := boxNode_bounds he ht (x+e/2)
      rw [indicator_of_mem hx,centeredBoxNode,Real.norm_eq_abs,abs_of_nonneg H.1]
      exact H.2
    · have H : x+e/2 ∉ Icc 0 (t+e) := fun h ↦ hx
        ⟨by linarith only [h.1], by linarith only [h.2]⟩
      rw [indicator_of_notMem hx,centeredBoxNode,boxNode_outside_support he ht H,norm_zero]

noncomputable def centeredBoxNodeL2 (e t : ℝ) (he : 0 < e) (ht : 0 ≤ t) :
    Lp ℝ 2 (volume : Measure ℝ) :=
  (memLp_centeredBoxNode he ht).toLp (centeredBoxNode e t)

theorem centeredBoxNode_L2_error {e t : ℝ} (he : 0 < e) (ht : 0 ≤ t) :
    ‖centeredBoxNodeL2 e t he ht-stepNodeL2 t‖^2 ≤ 2*e := by
  let f := centeredBoxNode e t
  let g := stepNode t
  let L := centeredBoxNodeL2 e t he ht-stepNodeL2 t
  have hL : (L : ℝ → ℝ) =ᵐ[volume] fun x ↦ f x-g x := by
    have hstepAE : (stepNodeL2 t : ℝ → ℝ) =ᵐ[volume] stepNode t :=
      MemLp.coeFn_toLp (f := stepNode t) (interval_one_memLp 0 t 2)
    filter_upwards [Lp.coeFn_sub (centeredBoxNodeL2 e t he ht) (stepNodeL2 t),
      (MemLp.coeFn_toLp (memLp_centeredBoxNode he ht)),
      hstepAE] with x hsub hbox hstep
    rw [Pi.sub_apply,show centeredBoxNodeL2 e t he ht x = f x from hbox,hstep] at hsub
    exact hsub
  have hinner : ‖L‖^2 = ∫ x, (f x-g x)^2 := by
    rw [← real_inner_self_eq_norm_sq,MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hL] with x hx
    rw [hx,real_inner_self_eq_norm_sq,Real.norm_eq_abs,sq_abs]
  have hInt (a b : ℝ) : Integrable ((Icc a b).indicator (fun _ ↦ (1:ℝ))) volume :=
    (memLp_one_iff_integrable).mp (interval_one_memLp a b 1)
  have hIntegral (a b : ℝ) (hab : a ≤ b) :
      (∫ x : ℝ, (Icc a b).indicator (fun _ ↦ (1:ℝ)) x) = b-a := by
    rw [integral_indicator measurableSet_Icc]
    simp [integral_const,Measure.real,Measure.restrict_apply MeasurableSet.univ,
      Real.volume_Icc,ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]
  rw [show ‖centeredBoxNodeL2 e t he ht-stepNodeL2 t‖^2 = ‖L‖^2 by rfl,hinner]
  calc
    _ ≤ ∫ x, (Icc (-e/2) (e/2)).indicator (fun _ ↦ (1:ℝ)) x +
        (Icc (t-e/2) (t+e/2)).indicator (fun _ ↦ (1:ℝ)) x :=
      integral_mono_of_nonneg (Eventually.of_forall fun _ ↦ sq_nonneg _)
        ((hInt _ _).add (hInt _ _)) (Eventually.of_forall (centeredBoxNode_sq_error_le_indicators he ht))
    _ = 2*e := by
      rw [integral_add (hInt _ _) (hInt _ _),hIntegral _ _ (by linarith),hIntegral _ _ (by linarith)]
      ring

theorem centeredBoxNode_L2_tendsto (e : ℕ → ℝ) (hp : ∀ n, 0 < e n)
    (he : Tendsto e atTop (𝓝 0)) {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun n ↦ centeredBoxNodeL2 (e n) t (hp n) ht) atTop (𝓝 (stepNodeL2 t)) := by
  apply Metric.tendsto_nhds.2
  intro δ hδ
  filter_upwards [he.eventually_lt_const (show 0 < δ^2/2 by positivity)] with n hn
  rw [dist_eq_norm]
  have H := centeredBoxNode_L2_error (hp n) ht
  nlinarith only [H, hn, hδ, norm_nonneg (centeredBoxNodeL2 (e n) t (hp n) ht-stepNodeL2 t)]

lemma boxRamp_mul_eq_clamp {e : ℝ} (he : 0 < e) (x : ℝ) :
    e * boxRamp e x = min e (max 0 x) := by
  rcases le_or_gt x 0 with hx|hx
  · rw [boxRamp_zero he hx,max_eq_left hx,min_eq_right he.le,mul_zero]
  rcases le_or_gt e x with hx'|hx'
  · rw [boxRamp_one he hx',max_eq_right hx.le,min_eq_left hx',mul_one]
  have hA : x/e ≤ 1 := (div_le_iff₀ he).2 (by simpa using hx'.le)
  unfold boxRamp
  rw [max_eq_right (div_nonneg hx.le he.le),min_eq_right hA,
    max_eq_right hx.le,min_eq_right hx'.le]
  field_simp

lemma clamp_sub_clamp_eq_intersection {e x y : ℝ} (he : 0 < e) (hyx : y ≤ x) :
    min e (max 0 x)-min e (max 0 y) = max 0 (min e x-max 0 y) := by
  rcases le_or_gt x 0 with hx|hx
  · have hy : y ≤ 0 := hyx.trans hx
    rw [max_eq_left hx,max_eq_left hy,min_eq_right he.le,min_eq_right (hx.trans he.le),
      sub_zero,sub_zero,max_eq_left hx]
  rcases le_or_gt e y with hy|hy
  · have hX : e ≤ x := hy.trans hyx
    rw [max_eq_right hx.le,max_eq_right (he.le.trans hy),min_eq_left hX,min_eq_left hy,
      sub_self,max_eq_left (sub_nonpos.mpr hy)]
  · have hy' : max 0 y ≤ e := max_le he.le hy.le
    have hXY : max 0 y ≤ min e x := le_min hy' (max_le hx.le hyx)
    rw [max_eq_right hx.le,min_eq_right hy',max_eq_right (sub_nonneg.mpr hXY)]

/-- Pointwise formula for convolution of the interval indicator with the
uniform probability density on the centered interval of width e. -/
theorem centeredBoxNode_eq_overlap {e t : ℝ} (he : 0 < e) (ht : 0 ≤ t) (x : ℝ) :
    centeredBoxNode e t x =
      ((volume : Measure ℝ) (Icc (-e/2) (e/2) ∩ Icc (x-t) x)).toReal/e := by
  have hSet : Icc (-e/2) (e/2) ∩ Icc (x-t) x =
      Icc (max (-e/2) (x-t)) (min (e/2) x) := by
    ext z
    simp only [mem_inter_iff,mem_Icc,max_le_iff,le_min_iff]
    tauto
  apply (eq_div_iff he.ne').2
  rw [hSet,Real.volume_Icc,ENNReal.toReal_ofReal', max_comm _ (0:ℝ)]
  rw [mul_comm,centeredBoxNode,boxNode,mul_sub,boxRamp_mul_eq_clamp he,boxRamp_mul_eq_clamp he,
    clamp_sub_clamp_eq_intersection he (by linarith)]
  congr 1
  have hm : min e (x+e/2) = min (e/2) x+e/2 := by
    rw [← min_add_add_right]
    congr 1 <;> ring
  have hM : max 0 (x+e/2-t) = max (-e/2) (x-t)+e/2 := by
    rw [← max_add_add_right]
    congr 1 <;> ring
  rw [hm,hM]
  ring

end CubeBrownian
#print axioms CubeBrownian.boxNode_L2_error
#print axioms CubeBrownian.centeredBoxNode_L2_tendsto
#print axioms CubeBrownian.centeredBoxNode_eq_overlap
