import TwoPoint
import Mathlib.MeasureTheory.Constructions.Pi

open MeasureTheory Set

namespace CenteredCube.RudinDensity

noncomputable def unitLaw : Measure ℝ := volume.restrict (Ioc 0 1)

instance : IsProbabilityMeasure unitLaw := by
  constructor
  simp [unitLaw, Measure.restrict_apply, Real.volume_Ioc]

noncomputable def cellLaw (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ => unitLaw)
instance (n : ℕ) : IsProbabilityMeasure (cellLaw n) := by
  unfold cellLaw
  infer_instance

theorem integral_unitLaw (f : ℝ → ℝ) :
    (∫ x, f x ∂unitLaw) = ∫ x in (0:ℝ)..1, f x := by
  rw [intervalIntegral.integral_of_le (by norm_num)]
  rfl

theorem score_law_mean (K : ℕ) (hK : 1 ≤ K) (t : ℝ) :
    ∫ x, normalizedScore K t x ∂unitLaw = 0 := by
  rw [integral_unitLaw, normalizedScore_mean K hK t]

theorem score_law_var (K : ℕ) (hK : 1 ≤ K) (t : ℝ) (hVt : 0 < VK K t) :
    ∫ x, normalizedScore K t x ^ 2 ∂unitLaw = 1 := by
  rw [integral_unitLaw, normalizedScore_sq K hK t hVt]

theorem pair_law_mean (K : ℕ) (hK : 1 ≤ K) (t s : ℝ) :
    ∫ x, sumScore K t s x ∂unitLaw = 0 := by
  rw [integral_unitLaw, sumScore_mean K hK t s]

theorem pair_law_var (K : ℕ) (hK : 1 ≤ K) (t s : ℝ) (hVt : 0 < VK K t)
    (hVs : 0 < VK K s) (hκ : 0 < 1 + kappa K t s) :
    ∫ x, sumScore K t s x ^ 2 ∂unitLaw = 1 := by
  rw [integral_unitLaw, sumScore_sq K hK t s hVt hVs hκ]

theorem sumScore_measurable (K : ℕ) (t s : ℝ) : Measurable (sumScore K t s) := by
  unfold sumScore
  exact (((normalizedScore_cont K t).add (normalizedScore_cont K s)).div_const _).measurable

theorem pair_measure_upper {K n : ℕ} (hn : 0 < n) {t s u : ℝ}
    (hκ : 0 < 1 + kappa K t s) :
    (cellLaw n).real
      ({v | u ≤ normalizedRow (normalizedScore K t) v} ∩
        {v | u ≤ normalizedRow (normalizedScore K s) v}) ≤
    (cellLaw n).real {v | pairThreshold K t s u ≤ normalizedRow (sumScore K t s) v} := by
  exact measureReal_mono (two_point_subset hn hκ)

end CenteredCube.RudinDensity

#print axioms CenteredCube.RudinDensity.pair_law_mean
#print axioms CenteredCube.RudinDensity.pair_law_var
#print axioms CenteredCube.RudinDensity.pair_measure_upper
