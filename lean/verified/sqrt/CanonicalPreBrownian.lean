import Mathlib.MeasureTheory.Constructions.KolmogorovExtension
import Mathlib.Probability.BrownianMotion.Basic

open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace CubeBrownian

noncomputable def paperWienerCylinder : Measure (ℝ≥0 → ℝ) :=
  projectiveLimit BrownianReal.projectiveFamily BrownianReal.isProjectiveMeasureFamily_projectiveFamily

instance : IsProbabilityMeasure paperWienerCylinder := by
  unfold paperWienerCylinder
  infer_instance

theorem paperWienerCylinder_isPreBrownian :
    IsPreBrownianReal (fun t : ℝ≥0 => fun x : ℝ≥0 → ℝ => x t) paperWienerCylinder := by
  constructor
  intro I
  exact ⟨I.measurable_restrict.aemeasurable,
    isProjectiveLimit_projectiveLimit BrownianReal.isProjectiveMeasureFamily_projectiveFamily I⟩

#print axioms paperWienerCylinder_isPreBrownian

end CubeBrownian
