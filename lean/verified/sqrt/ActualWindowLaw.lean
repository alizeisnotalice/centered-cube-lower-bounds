import TrueTiltPeriod
import TrueTiltProductLaw
import SqrtActualWindowCentered
import SqrtActualLocalVariance

open MeasureTheory ProbabilityTheory
open scoped Interval BigOperators
open CenteredCubeSqrt
namespace CubeSqrtProbability

/-- Exact one-coordinate law facts for the true manuscript window density. -/
theorem actual_window_amplitude_and_centering {B K : ℕ} [NeZero K]
    (f : ZMod K → Fin B) (M : ℕ) (p : ℝ) (hB : 0<B) (hk : 2≤K)
    {δ L : ℝ} (hδ0 : 0<δ) (hδ : δ<1/((B:ℝ)*K)) (hL : 1≤L) :
    let d := actualWindowPerturbation f M p δ L
    Measurable d ∧ (∫ w, d w ∂unitPeriodLaw)=0 ∧ ∀ w, |d w| ≤ 7*|p|/(K:ℝ) := by
  dsimp
  have hLp : 0<L := by linarith
  have hK : 0 < (K:ℝ) := by exact_mod_cast (show 0 < K by omega)
  have hKL : 0 < (K:ℝ)*L := mul_pos hK hLp
  refine ⟨?_, ?_, ?_⟩
  · exact (show Continuous (actualWindowPerturbation f M p δ L) from by
      simp_rw [show actualWindowPerturbation f M p δ L =
        (fun w ↦ (p/((K:ℝ)*L))*(actualAtomicWindow f δ L w+actualLowSpectrum M L w)) from
          funext (actualWindowPerturbation_formula f M p hδ0 hLp)]
      exact continuous_const.mul ((actualAtomicWindow_continuous f hδ0 L).add
        (actualLowSpectrum_continuous M L))).measurable
  · rw [unitPeriod_integral]
    exact actualWindowPerturbation_integral_zero f M p hB hk hδ0 hδ hLp
  · intro w
    rw [actualWindowPerturbation_formula f M p hδ0 hLp,abs_mul,abs_div,abs_of_pos hKL]
    calc
      _ ≤ (|p|/((K:ℝ)*L))*7 := mul_le_mul_of_nonneg_left
        (actual_compensated_window_abs_le_seven f M hB hk hδ0 hδ w) (by positivity)
      _ ≤ 7*|p|/(K:ℝ) := by
        have h : (|p|/(K:ℝ))/L≤|p|/(K:ℝ) := (div_le_iff₀ hLp).2 (by nlinarith [show 0≤|p|/(K:ℝ) by positivity])
        rw [← div_div]
        rw [mul_div_assoc]
        linarith

theorem actual_window_raw_sq (d : ℝ → ℝ) :
    rawSq unitPeriodLaw d = periodL2Sq d :=
  unitPeriod_rawSq d

end CubeSqrtProbability

#print axioms CubeSqrtProbability.actual_window_amplitude_and_centering
#print axioms CubeSqrtProbability.actual_window_raw_sq
