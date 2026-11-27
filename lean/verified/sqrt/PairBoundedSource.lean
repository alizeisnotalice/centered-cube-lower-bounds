import AffinityTransfer
import TrueTiltIntegratedMean
import Mathlib.Tactic
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology ProbabilityTheory
namespace CubeSqrtPair

noncomputable def linearPair {Ω : Type*} (d e : Ω → ℝ) : Ω → ℝ :=
  fun w ↦ (d w+e w)/2

noncomputable def logPair {Ω : Type*} (d e : Ω → ℝ) : Ω → ℝ :=
  pairScore (fun w ↦ Real.log (1+d w)) (fun w ↦ Real.log (1+e w))

theorem exp_logPair_eq_hellinger {Ω : Type*} (d e : Ω → ℝ) (a : ℝ) (ha : a ≤ 1/2)
    (hd : ∀ w, |d w| ≤ a) (he : ∀ w, |e w| ≤ a) (w : Ω) :
    Real.exp (logPair d e w) = Real.sqrt ((1+d w)*(1+e w)) := by
  have hd' : 0 < 1+d w := by linarith only [ha,(abs_le.mp (hd w)).1]
  have he' : 0 < 1+e w := by linarith only [ha,(abs_le.mp (he w)).1]
  dsimp only [logPair,pairScore]
  rw [← Real.log_mul hd'.ne' he'.ne',Real.sqrt_eq_rpow,Real.rpow_def_of_pos (mul_pos hd' he')]
  congr 1
  ring

theorem logPair_abs_le_two_mul_amp {Ω : Type*} (d e : Ω → ℝ) (a : ℝ)
    (ha : a ≤ 1/2) (hd : ∀ w, |d w| ≤ a) (he : ∀ w, |e w| ≤ a) (w : Ω) :
    |logPair d e w| ≤ 2*a := by
  have hD := (CubeSqrtProbability.log1p_abs_le ha (hd w)).trans
    (mul_le_mul_of_nonneg_left (hd w) (by norm_num : (0:ℝ) ≤ 2))
  have hE := (CubeSqrtProbability.log1p_abs_le ha (he w)).trans
    (mul_le_mul_of_nonneg_left (he w) (by norm_num : (0:ℝ) ≤ 2))
  dsimp only [logPair,pairScore]
  rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
  exact (div_le_iff₀ (by norm_num : (0:ℝ)<2)).2
    ((abs_add_le _ _).trans (by linarith only [hD,hE]))

theorem logPair_density_ratio_bounds
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (d e : Ω → ℝ) (hmd : Measurable d) (hme : Measurable e)
    (a : ℝ) (ha : a ≤ 1/2) (hd : ∀ w, |d w| ≤ a) (he : ∀ w, |e w| ≤ a) :
    let V := logPair d e
    let H := ∫ w, Real.exp (V w) ∂P
    Integrable (fun w ↦ Real.exp (V w)) P ∧
      (∀ w, (1-a)/(1+a) ≤ Real.exp (V w)/H ∧ Real.exp (V w)/H ≤ (1+a)/(1-a)) := by
  dsimp only
  let V := logPair d e
  let H := ∫ w, Real.exp (V w) ∂P
  have hV : Measurable V := by unfold V logPair pairScore; fun_prop
  have hAE (w : Ω) : 1-a ≤ Real.exp (V w) ∧ Real.exp (V w) ≤ 1+a := by
    rw [exp_logPair_eq_hellinger d e a ha hd he w]
    have ha0 : 0 ≤ a := (abs_nonneg _).trans (hd w)
    have haL : 0 ≤ 1-a := by linarith only [ha]
    have hdl : 1-a ≤ 1+d w := by linarith only [(abs_le.mp (hd w)).1]
    have hel : 1-a ≤ 1+e w := by linarith only [(abs_le.mp (he w)).1]
    have hdu : 1+d w ≤ 1+a := by linarith only [(abs_le.mp (hd w)).2]
    have heu : 1+e w ≤ 1+a := by linarith only [(abs_le.mp (he w)).2]
    have hL := Real.sqrt_le_sqrt (mul_le_mul hdl hel haL (haL.trans hdl))
    have hU := Real.sqrt_le_sqrt (mul_le_mul hdu heu (haL.trans hel) (by linarith only [ha0]))
    rw [← sq,Real.sqrt_sq haL] at hL
    rw [← sq,Real.sqrt_sq (by linarith only [ha0])] at hU
    exact ⟨hL,hU⟩
  have hI : Integrable (fun w ↦ Real.exp (V w)) P := by
    apply (integrable_const (1+a)).mono' (Real.measurable_exp.comp hV).aestronglyMeasurable
    exact Eventually.of_forall fun w ↦ by
      change ‖Real.exp (V w)‖ ≤ 1+a
      rw [Real.norm_eq_abs,abs_of_nonneg (Real.exp_pos _).le]
      exact (hAE w).2
  have hH : (1-a) ≤ H ∧ H ≤ (1+a) := by
    have hL := integral_mono_ae (integrable_const (1-a)) hI
      (Eventually.of_forall fun w ↦ (hAE w).1)
    have hU := integral_mono_ae hI (integrable_const (1+a))
      (Eventually.of_forall fun w ↦ (hAE w).2)
    exact ⟨by simpa [H] using hL,by simpa [H] using hU⟩
  have hHp : 0 < H := (by linarith only [ha] : 0 < 1-a).trans_le hH.1
  refine ⟨hI,fun w ↦ ?_⟩
  constructor
  · calc
      _ ≤ (1-a)/H := div_le_div_of_nonneg_left (by linarith only [ha]) hHp hH.2
      _ ≤ _ := div_le_div_of_nonneg_right (hAE w).1 hHp.le
  · calc
      _ ≤ (1+a)/H := div_le_div_of_nonneg_right (hAE w).2 hHp.le
      _ ≤ _ := div_le_div_of_nonneg_left ((Real.exp_pos _).le.trans (hAE w).2)
        (by linarith only [ha]) hH.1

/-- Squared pointwise envelope for the difference of the logarithmic and
linear two-point scores, using the actual log of the bounded perturbation. -/
theorem logPair_linear_error_sq {Ω : Type*} (d e : Ω → ℝ) (a : ℝ)
    (ha : a ≤ 1/2) (hd : ∀ w, |d w| ≤ a) (he : ∀ w, |e w| ≤ a) (w : Ω) :
    (logPair d e w-linearPair d e w)^2 ≤ 2*a^2*((d w)^2+(e w)^2) := by
  have ha0 : 0 ≤ a := (abs_nonneg _).trans (hd w)
  have hLog (x : ℝ) (hx : |x| ≤ a) : |Real.log (1+x)-x| ≤ a*2*|x| := by
    have hq := CubeSqrtProbability.log1p_quadratic_approx ha hx
    have hx2 : x^2 ≤ a*|x| := by
      rw [← sq_abs,pow_two]
      exact mul_le_mul_of_nonneg_right hx (abs_nonneg _)
    have ht : |Real.log (1+x)-x| ≤ 2*a*x^2+x^2/2 := by
      have heq : Real.log (1+x)-x=(Real.log (1+x)-(x-x^2/2))-x^2/2 := by ring
      rw [heq]
      exact (abs_sub _ _).trans (by rw [abs_of_nonneg (by positivity : 0 ≤ x^2/2)]; linarith only [hq])
    have h0 : 0 ≤ 1-2*a := by linarith only [ha]
    have hp := mul_nonneg h0 (sq_nonneg x)
    calc
      _ ≤ 2*x^2 := by nlinarith only [ht,hp,sq_nonneg x]
      _ ≤ _ := by nlinarith only [hx2]
  have hA : |logPair d e w-linearPair d e w| ≤ a*(|d w|+|e w|) := by
    have heq : logPair d e w-linearPair d e w =
        ((Real.log (1+d w)-d w)+(Real.log (1+e w)-e w))/2 := by
      dsimp only [logPair,pairScore,linearPair]
      ring
    rw [heq,abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
    exact (div_le_iff₀ (by norm_num : (0:ℝ)<2)).2
      ((abs_add_le _ _).trans (by linarith only [hLog _ (hd w),hLog _ (he w)]))
  have hB := pow_le_pow_left₀ (abs_nonneg _) hA 2
  rw [sq_abs,mul_pow] at hB
  refine hB.trans ?_
  calc
    _ ≤ a^2*(2*((d w)^2+(e w)^2)) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      nlinarith only [sq_nonneg (|d w|-|e w|),sq_abs (d w),sq_abs (e w)]
    _ = _ := by ring

end CubeSqrtPair
#print axioms CubeSqrtPair.logPair_density_ratio_bounds
#print axioms CubeSqrtPair.logPair_linear_error_sq
