import SqrtActualWindowCentered
import SqrtWindowUniformBounds
import SqrtWitnessGramCauchy
import TrueTiltPeriod
import Mathlib.Probability.Moments.Covariance

namespace CenteredCubeSqrt
open MeasureTheory ProbabilityTheory CubeSqrtProbability Set Filter
open scoped ProbabilityTheory Interval

noncomputable def actualPaperPairMoment {B K : ℕ} [NeZero K]
    (f : ZMod K → Fin B) (M n : ℕ) (p δ L : ℝ) : ℝ :=
  (n:ℝ)*(p/((K:ℝ)*L))^2*actualWitnessGram f M δ L L

theorem actual_windowPerturbation_continuous {B K : ℕ} [NeZero K]
    (f : ZMod K → Fin B) (M : ℕ) (p : ℝ) {δ L : ℝ} (hδ : 0<δ) (hL : 0<L) :
    Continuous (actualWindowPerturbation f M p δ L) := by
  rw [show actualWindowPerturbation f M p δ L =
     fun x => (p/((K:ℝ)*L))*(actualAtomicWindow f δ L x+actualLowSpectrum M L x) from
    funext (actualWindowPerturbation_formula f M p hδ hL)]
  exact ((actualAtomicWindow_continuous f hδ L).add (actualLowSpectrum_continuous M L)).const_mul _

theorem actual_windowPerturbation_period_product {B K : ℕ} [NeZero K]
    (f : ZMod K → Fin B) (M : ℕ) (p : ℝ) {δ L J : ℝ}
    (hδ : 0<δ) (hL : 0<L) (hJ : 0<J) :
    (∫ x, actualWindowPerturbation f M p δ L x * actualWindowPerturbation f M p δ J x ∂unitPeriodLaw) =
      (p/((K:ℝ)*L))*(p/((K:ℝ)*J))*actualWitnessGram f M δ L J := by
  rw [unitPeriod_integral]
  let F (x : ℝ) := actualAtomicWindow f δ L x+actualLowSpectrum M L x
  let G (x : ℝ) := actualAtomicWindow f δ J x+actualLowSpectrum M J x
  have e : (fun x => actualWindowPerturbation f M p δ L x * actualWindowPerturbation f M p δ J x) =
      fun x => ((p/((K:ℝ)*L))*(p/((K:ℝ)*J)))*(F x*G x) := by
    funext x
    rw [actualWindowPerturbation_formula f M p hδ hL, actualWindowPerturbation_formula f M p hδ hJ]
    change _ * F x * (_ * G x) = _
    ring
  rw [e, intervalIntegral.integral_const_mul]
  rfl

theorem actual_paper_pair_moment_eq {B K : ℕ} [NeZero K]
    (f : ZMod K → Fin B) (M n : ℕ) (p : ℝ) {δ L : ℝ}
    (hδ : 0<δ) (hL : 0<L) :
    actualPaperPairMoment f M n p δ L =
      (n:ℝ)*(∫ x, (actualWindowPerturbation f M p δ L x)^2 ∂unitPeriodLaw) := by
  simp_rw [pow_two]
  rw [actual_windowPerturbation_period_product f M p hδ hL hL,actualPaperPairMoment]
  ring

theorem actual_windowPerturbation_period_covariance {B K : ℕ} [NeZero K]
    (f : ZMod K → Fin B) (M : ℕ) (p : ℝ) (hB : 0<B) (hK : 2≤K)
    {δ L J a : ℝ} (hδ : 0<δ) (hδB : δ<1/((B:ℝ)*K))
    (hL : 0<L) (hJ : 0<J)
    (hcapL : ∀ x, |actualWindowPerturbation f M p δ L x|≤a)
    (hcapJ : ∀ x, |actualWindowPerturbation f M p δ J x|≤a) :
    cov[actualWindowPerturbation f M p δ L,actualWindowPerturbation f M p δ J;unitPeriodLaw] =
       (p/((K:ℝ)*L))*(p/((K:ℝ)*J))*actualWitnessGram f M δ L J := by
  have lp (U : ℝ) (hU : 0<U) (hcap : ∀ x, |actualWindowPerturbation f M p δ U x|≤a) :
      MemLp (actualWindowPerturbation f M p δ U) 2 unitPeriodLaw :=
    MemLp.of_bound (actual_windowPerturbation_continuous f M p hδ hU).aestronglyMeasurable a
      (Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hcap x)
  have hz (U : ℝ) (hU : 0<U) : (∫ x, actualWindowPerturbation f M p δ U x ∂unitPeriodLaw)=0 := by
    rw [unitPeriod_integral]
    exact actualWindowPerturbation_integral_zero f M p hB hK hδ hδB hU
  rw [covariance_eq_sub (lp L hL hcapL) (lp J hJ hcapJ),hz L hL,hz J hJ,zero_mul,sub_zero]
  exact actual_windowPerturbation_period_product f M p hδ hL hJ

theorem actual_paper_pair_moment_ratio {B K : ℕ} [NeZero K]
    (f : ZMod K → Fin B) (M n : ℕ) (p δ : ℝ) {L v : ℝ} (hL : 0<L)
    (hv : v=(n:ℝ)*(p/(K:ℝ))^2*(9/29)) :
    actualPaperPairMoment f M n p δ L =
      v*(actualWitnessGram f M δ L L/((27/29)*L^2/3)) := by
  have hk : (K:ℝ)≠0 := by exact_mod_cast NeZero.ne K
  rw [hv,actualPaperPairMoment]
  field_simp [hk,hL.ne']
  ring

theorem actual_windowPerturbation_uniform_cap {B K : ℕ} [NeZero K]
    (f : ZMod K → Fin B) (M : ℕ) {p δ L : ℝ} (hB : 0<B) (hK : 2≤K)
    (hp : 0≤p) (hδ : 0<δ) (hδB : δ<1/((B:ℝ)*K)) (hL : 1≤L) (x : ℝ) :
    |actualWindowPerturbation f M p δ L x| ≤ 7*p/(K:ℝ) := by
  have hKR : 0<(K:ℝ) := by exact_mod_cast (show 0<K by omega)
  have hL0 : 0 < L := by linarith
  have hca : 0≤p/((K:ℝ)*L) := by positivity
  rw [actualWindowPerturbation_formula f M p hδ hL0,abs_mul,abs_of_nonneg hca]
  have hcf : p/((K:ℝ)*L) ≤ p/(K:ℝ) :=
    div_le_div_of_nonneg_left hp hKR (by nlinarith only [hKR,hL])
  have t := mul_le_mul hcf (actual_compensated_window_abs_le_seven (L:=L) f M hB hK hδ hδB x) (abs_nonneg _) (by positivity)
  refine t.trans_eq ?_
  ring

#print axioms actual_windowPerturbation_uniform_cap
#print axioms actual_windowPerturbation_period_covariance
#print axioms actual_paper_pair_moment_eq
#print axioms actual_paper_pair_moment_ratio
end CenteredCubeSqrt
