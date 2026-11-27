import ActualPairMoments
import SqrtActualKernelBundle

namespace CenteredCubeSqrt
open MeasureTheory ProbabilityTheory CubeSqrtProbability Set Filter
open scoped ProbabilityTheory Interval

theorem actual_paper_pair_cov_normalized {B K : ℕ} [NeZero K]
    (f : ZMod K → Fin B) (M n : ℕ) {p : ℝ} (hp : 0<p) (hB : 0<B) (hK : 2≤K)
    {δ L J a : ℝ} (hδ : 0<δ) (hδB : δ<1/((B:ℝ)*K))
    (hL : 0<L) (hJ : 0<J)
    (hcapL : ∀ x, |actualWindowPerturbation f M p δ L x|≤a)
    (hcapJ : ∀ x, |actualWindowPerturbation f M p δ J x|≤a)
    (hGL : 0<actualWitnessGram f M δ L L)
    (hGJ : 0<actualWitnessGram f M δ J J) :
    (n:ℝ)*cov[actualWindowPerturbation f M p δ L,actualWindowPerturbation f M p δ J;unitPeriodLaw] =
      Real.sqrt (actualPaperPairMoment f M n p δ L)*Real.sqrt (actualPaperPairMoment f M n p δ J)*
        actualNormalizedGram f M δ L J := by
  let c := p/((K:ℝ)*L)
  let e := p/((K:ℝ)*J)
  let g := actualWitnessGram f M δ L L
  let k := actualWitnessGram f M δ J J
  let w := actualWitnessGram f M δ L J
  have hc : 0≤c := by unfold c; positivity
  have he : 0≤e := by unfold e; positivity
  have hg : 0<g := hGL
  have hk : 0<k := hGJ
  rw [actual_windowPerturbation_period_covariance f M p hB hK hδ hδB hL hJ hcapL hcapJ]
  change (n:ℝ)*(c*e*w)=Real.sqrt ((n:ℝ)*c^2*g)*Real.sqrt ((n:ℝ)*e^2*k)*(w/Real.sqrt (g*k))
  rw [Real.sqrt_mul (mul_nonneg (Nat.cast_nonneg n) (sq_nonneg c)),
    Real.sqrt_mul (mul_nonneg (Nat.cast_nonneg n) (sq_nonneg e)),
    Real.sqrt_mul (Nat.cast_nonneg n), Real.sqrt_mul (Nat.cast_nonneg n),
    Real.sqrt_sq hc,Real.sqrt_sq he, Real.sqrt_mul hg.le]
  have hcanc : Real.sqrt (n:ℝ)*Real.sqrt (n:ℝ)=(n:ℝ) := Real.mul_self_sqrt (Nat.cast_nonneg _)
  field_simp [(Real.sqrt_pos.2 hg).ne',(Real.sqrt_pos.2 hk).ne']
  linear_combination - (c*e*w)*hcanc

theorem actual_normalizedGram_le_one_from_positive {B K : ℕ} [NeZero K]
    (f : ZMod K → Fin B) (M : ℕ) {δ : ℝ} (hδ : 0<δ) (L J : ℝ)
    (hGL : 0<actualWitnessGram f M δ L L)
    (hGJ : 0<actualWitnessGram f M δ J J) :
    actualNormalizedGram f M δ L J ≤ 1 := by
  unfold actualNormalizedGram
  apply (div_le_one (Real.sqrt_pos.2 (mul_pos hGL hGJ))).2
  exact (le_abs_self _).trans (witnessGram_entry_cauchy f M hδ L J)

theorem actual_pair_moment_lower_of_relative {B K : ℕ} [NeZero K]
    (f : ZMod K → Fin B) (M n : ℕ) (p δ : ℝ) {L v C R : ℝ} (hL : 0<L)
    (hv : v=(n:ℝ)*(p/(K:ℝ))^2*(9/29)) (hv0 : 0≤v)
    (hR : v*R ≤ C) (h : |actualWitnessGram f M δ L L/((27/29)*L^2/3)-1|≤R) :
    v-C≤actualPaperPairMoment f M n p δ L := by
  rw [actual_paper_pair_moment_ratio f M n p δ hL hv]
  have h' := mul_le_mul_of_nonneg_left (abs_le.mp h).1 hv0
  linarith only [hR,h']

#print axioms actual_paper_pair_cov_normalized
#print axioms actual_pair_moment_lower_of_relative
end CenteredCubeSqrt
