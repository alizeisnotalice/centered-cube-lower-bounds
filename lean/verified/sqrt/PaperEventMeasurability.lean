import ActualPaperPairBound

namespace CenteredCubeSqrt
open MeasureTheory ProbabilityTheory Set Filter CubeSqrtProbability
open scoped ProbabilityTheory Interval

theorem actualPaperScaleEvent_measurable {B K : ℕ} [NeZero K] (f : ZMod K → Fin B)
    (M n : ℕ) (p h : ℝ) {δ L : ℝ} (hδ : 0<δ) (hL : 0<L) :
    MeasurableSet (actualPaperScaleEvent f M n p δ h L) := by
  unfold actualPaperScaleEvent
  apply measurableSet_lt measurable_const
  exact Finset.measurable_sum _ (fun i _ =>
    Real.measurable_log.comp ((actual_windowPerturbation_continuous f M p hδ hL).measurable.const_add 1
      |>.comp (measurable_pi_apply i)))

#print axioms actualPaperScaleEvent_measurable
end CenteredCubeSqrt
