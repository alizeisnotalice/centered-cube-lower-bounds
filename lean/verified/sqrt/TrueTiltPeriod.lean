import TrueTiltPolarization
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open MeasureTheory Filter Set Topology
namespace CubeSqrtProbability

noncomputable def unitPeriodLaw : Measure ℝ :=
  volume.restrict (Ioc 0 1)

instance unitPeriodLaw_isProbabilityMeasure : IsProbabilityMeasure unitPeriodLaw := by
  constructor
  simp [unitPeriodLaw, Real.volume_Ioc]

theorem unitPeriod_integral (f : ℝ → ℝ) :
    (∫ w, f w ∂unitPeriodLaw) = ∫ w in (0:ℝ)..1, f w := by
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  rfl

theorem unitPeriod_rawSq (f : ℝ → ℝ) :
    rawSq unitPeriodLaw f = ∫ w in (0:ℝ)..1, (f w)^2 :=
  unitPeriod_integral _

theorem unitPeriod_rawIncCross (X Y Z : ℝ → ℝ) :
    rawIncCross unitPeriodLaw X Y Z =
      ∫ w in (0:ℝ)..1, (Y w-X w)*(Z w-X w) :=
  unitPeriod_integral _

end CubeSqrtProbability
#print axioms CubeSqrtProbability.unitPeriodLaw_isProbabilityMeasure
#print axioms CubeSqrtProbability.unitPeriod_integral
#print axioms CubeSqrtProbability.unitPeriod_rawSq
#print axioms CubeSqrtProbability.unitPeriod_rawIncCross
