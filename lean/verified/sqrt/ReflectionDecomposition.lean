import JointReflectionReduction

open MeasureTheory Set
namespace CubeBrownian

theorem reflect_endpoint_decompose {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (E : Set Ω) (Z : Ω → ℝ) (a : ℝ)
    (_hE : MeasurableSet E) (hZ : Measurable Z)
    (hSub : Z ⁻¹' Ioi a ⊆ E) (hAtom : μ (Z ⁻¹' {a}) = 0)
    (hSym : ∀ z, μ (E ∩ Z ⁻¹' Iic z) =
      μ (E ∩ (fun w ↦ 2*a-Z w) ⁻¹' Iic z)) :
    (μ.restrict E).map Z =
      (μ.map Z).restrict (Ioi a) +
        ((μ.map Z).restrict (Ioi a)).map (fun z ↦ 2*a-z) := by
  let N := (μ.restrict E).map Z
  let R : ℝ → ℝ := fun z ↦ 2*a-z
  have hR : Measurable R := by dsimp [R]; fun_prop
  have hRZ : Measurable (R ∘ Z) := hR.comp hZ
  have hS : N.map R = N := by
    apply Measure.ext_of_Iic
    intro z
    dsimp only [N]
    rw [Measure.map_map hR hZ, Measure.map_apply hRZ measurableSet_Iic,
      Measure.map_apply hZ measurableSet_Iic, Measure.restrict_apply (hRZ measurableSet_Iic),
      Measure.restrict_apply (hZ measurableSet_Iic), inter_comm _ E, inter_comm _ E]
    exact (hSym z).symm
  have hU : N.restrict (Ioi a) = (μ.map Z).restrict (Ioi a) := by
    ext s hs
    rw [Measure.restrict_apply hs, Measure.restrict_apply hs,
      show N (s ∩ Ioi a) = (μ.restrict E).map Z (s ∩ Ioi a) by rfl,
      Measure.map_apply hZ (hs.inter measurableSet_Ioi),
      Measure.map_apply hZ (hs.inter measurableSet_Ioi),
      Measure.restrict_apply (hZ (hs.inter measurableSet_Ioi))]
    congr 1
    exact inter_eq_left.mpr (fun x hx ↦ hSub hx.2)
  have haN : N {a} = 0 := by
    dsimp only [N]
    rw [Measure.map_apply hZ (measurableSet_singleton a),
      Measure.restrict_apply (hZ (measurableSet_singleton a))]
    exact measure_mono_null inter_subset_left hAtom
  have hp : R ⁻¹' Iio a = Ioi a := by
    ext x
    change 2*a-x < a ↔ a < x
    constructor <;> intro h <;> linarith
  have hL : N.restrict (Iio a) = (N.restrict (Ioi a)).map R := by
    ext s hs
    calc
      N.restrict (Iio a) s = N (s ∩ Iio a) := Measure.restrict_apply hs
      _ = (N.map R) (s ∩ Iio a) := by rw [hS]
      _ = N (R ⁻¹' s ∩ Ioi a) := by
        rw [Measure.map_apply hR (hs.inter measurableSet_Iio), preimage_inter, hp]
      _ = ((N.restrict (Ioi a)).map R) s := by
        rw [Measure.map_apply hR hs, Measure.restrict_apply (hR hs)]
  have hi : N.restrict (Iic a) = N.restrict (Iio a) :=
    Measure.restrict_congr_set (Iio_ae_eq_Iic' haN).symm
  calc
    N = N.restrict (Ioi a) + N.restrict (Iic a) := by
      simpa only [compl_Ioi] using (Measure.restrict_add_restrict_compl
        (μ := N) measurableSet_Ioi).symm
    _ = _ := by rw [hi, hL, hU]

end CubeBrownian
#print axioms CubeBrownian.reflect_endpoint_decompose
