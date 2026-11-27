import ProbabilityScores
import Mathlib.Analysis.SpecialFunctions.Exp

open MeasureTheory Set

namespace CenteredCube.RudinDensity

theorem pair_threshold_lower {K : ℕ} {t s u : ℝ} (hu : 0 ≤ u)
    (hκ : 0 < 1 + kappa K t s) (hκ' : kappa K t s ≤ 1) :
    u ≤ pairThreshold K t s u := by
  have hpos : 0 < Real.sqrt (2 * (1 + kappa K t s)) := Real.sqrt_pos.2 (by positivity)
  have h₂ : Real.sqrt (2 * (1 + kappa K t s)) ≤ 2 := by
    have H := Real.sqrt_le_sqrt (show 2*(1+kappa K t s) ≤ 4 by linarith)
    have hsq : Real.sqrt (4:ℝ) = 2 := by norm_num
    exact H.trans_eq hsq
  unfold pairThreshold
  apply (le_div_iff₀ hpos).2
  simpa [mul_comm] using mul_le_mul_of_nonneg_left h₂ hu

theorem pair_threshold_upper {K : ℕ} {t s u ε : ℝ} (hu : 0 ≤ u)
    (hε : 0 < ε) (hκ : ε ≤ 1 + kappa K t s) :
    pairThreshold K t s u ≤ 2*u / Real.sqrt (2*ε) := by
  unfold pairThreshold
  exact div_le_div_of_nonneg_left (by positivity) (Real.sqrt_pos.2 (by positivity))
    (Real.sqrt_le_sqrt (by linarith))

theorem two_point_numeric {K n : ℕ} (hn : 0 < n) {t s u A e : ℝ}
    (hu : 0 < u) (hA : 0 ≤ A) (he : e ≤ 1)
    (hκ : 0 < 1 + kappa K t s) (hκ' : kappa K t s ≤ 1)
    (hMD : (cellLaw n).real
          {v | pairThreshold K t s u ≤ normalizedRow (sumScore K t s) v}
          ≤ A / pairThreshold K t s u *
            Real.exp (-(pairThreshold K t s u)^2/2 + e)) :
    (cellLaw n).real
      ({v | u ≤ normalizedRow (normalizedScore K t) v} ∩
        {v | u ≤ normalizedRow (normalizedScore K s) v}) ≤
      (Real.exp 1*A)/u * Real.exp (-(u^2)/(1+kappa K t s)) := by
  have hw := pair_threshold_lower hu.le hκ hκ'
  have hprefix : A / pairThreshold K t s u ≤ A/u :=
    div_le_div_of_nonneg_left hA hu hw
  have ht : -(pairThreshold K t s u)^2/2 = -(u^2)/(1+kappa K t s) := by
    have h := pairThreshold_exponent (u := u) hκ
    simpa only [neg_div] using congrArg (fun x : ℝ => -x) h
  have hexp : Real.exp (-(pairThreshold K t s u)^2/2+e) ≤
      Real.exp (-(u^2)/(1+kappa K t s)) * Real.exp 1 := by
    rw [← Real.exp_add, Real.exp_le_exp, ht]
    linarith
  calc
    _ ≤ _ := (pair_measure_upper hn hκ).trans hMD
    _ ≤ (A/u) * (Real.exp (-(u^2)/(1+kappa K t s)) * Real.exp 1) :=
      mul_le_mul hprefix hexp (Real.exp_pos _).le (by positivity)
    _ = _ := by ring

end CenteredCube.RudinDensity

#print axioms CenteredCube.RudinDensity.two_point_numeric
