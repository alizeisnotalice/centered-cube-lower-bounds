import SqrtWindowHarmonicFubini
namespace CenteredCubeSqrt
open MeasureTheory Set
open scoped Interval
set_option maxHeartbeats 1000000

theorem triangular_prefix_Fubini {f : ℝ→ℝ} (hf : Measurable f) {a b C : ℝ}
    (hab : a≤b) (hC : ∀ x∈Icc a b, |f x|≤C) :
    (∫ x in a..b, ∫ y in a..x,f y) =
      ∫ y in a..b,(b-y)*f y := by
  let I := (volume : Measure ℝ).restrict (Ioc a b)
  let : IsFiniteMeasure I := ⟨by unfold I; rw [Measure.restrict_apply_univ]; simp [Real.volume_Ioc]⟩
  let H (x y : ℝ) := if y≤x then f y else 0
  have hMeas : Measurable (Function.uncurry H) := by
    have hs : MeasurableSet {p : ℝ×ℝ | p.2≤p.1} := measurableSet_le measurable_snd measurable_fst
    exact Measurable.ite hs (hf.comp measurable_snd) measurable_const
  have hC0 : 0≤C := (abs_nonneg _).trans (hC a ⟨le_rfl,hab⟩)
  have hmem : ∀ᵐ z ∂I.prod I,z.2∈Ioc a b :=
    (Measure.ae_prod_iff_ae_ae (p:=fun z : ℝ×ℝ => z.2∈Ioc a b) (measurable_snd measurableSet_Ioc)).mpr
      (Filter.Eventually.of_forall (fun _ => ae_restrict_mem measurableSet_Ioc))
  have hInt : Integrable (Function.uncurry H) (I.prod I) := by
    apply integrableOn_univ.mp
    apply Measure.integrableOn_of_bounded (M:=C) (s_finite:=(measure_lt_top _ univ).ne) hMeas.aestronglyMeasurable
    simp only [Measure.restrict_univ]
    filter_upwards [hmem] with z hz
    change ‖if z.2≤z.1 then f z.2 else 0‖≤C
    split
    · rw [Real.norm_eq_abs]; exact hC _ ⟨hz.1.le,hz.2⟩
    · rw [norm_zero]; exact hC0
  have hleft (x : ℝ) (hx : x∈Ioc a b) : (∫ y in a..x,f y) = ∫ y, H x y ∂I := by
    have ei : H x = (Iic x).indicator f := by
      funext y
      by_cases h : y≤x <;> simp [H,h]
    rw [intervalIntegral.integral_of_le hx.1.le,ei,integral_indicator measurableSet_Iic]
    unfold I
    rw [Measure.restrict_restrict measurableSet_Iic]
    have es : Iic x ∩ Ioc a b=Ioc a x := by
      ext y
      simp only [mem_inter_iff,mem_Iic,mem_Ioc]
      exact ⟨fun h => ⟨h.2.1,h.1⟩,fun h => ⟨h.2,h.1,h.2.trans hx.2⟩⟩
    rw [es]
  have hright (y : ℝ) (hy : y∈Ioc a b) : (∫ x, H x y ∂I) = (b-y)*f y := by
    have ei : (fun x => H x y) = (Ici y).indicator (fun _ : ℝ => f y) := by
      funext x
      by_cases h : y≤x <;> simp [H,h]
    rw [ei,integral_indicator measurableSet_Ici]
    unfold I
    rw [Measure.restrict_restrict measurableSet_Ici]
    have es : Ici y ∩ Ioc a b=Icc y b := by
      ext x
      simp only [mem_inter_iff,mem_Ici,mem_Ioc,mem_Icc]
      exact ⟨fun h => ⟨h.1,h.2.2⟩,fun h => ⟨h.1,hy.1.trans_le h.1,h.2⟩⟩
    rw [es,setIntegral_const,measureReal_def,Real.volume_Icc,ENNReal.toReal_ofReal (sub_nonneg.mpr hy.2),smul_eq_mul]
  simp_rw [show (∫ x in a..b, ∫ y in a..x, f y)=(∫ x, (∫ y in a..x,f y) ∂I) from
    intervalIntegral.integral_of_le hab,
    show (∫ y in a..b, (b-y)*f y)=(∫ y, (b-y)*f y ∂I) from intervalIntegral.integral_of_le hab]
  have Hleft : (∫ x, (∫ y in a..x,f y) ∂I) = ∫ x, ∫ y, H x y ∂I ∂I :=
    integral_congr_ae ((ae_restrict_mem measurableSet_Ioc).mono hleft)
  rw [Hleft,integral_integral_swap hInt]
  exact integral_congr_ae ((ae_restrict_mem measurableSet_Ioc).mono hright)

#print axioms triangular_prefix_Fubini
end CenteredCubeSqrt
