import PairBoundedSource
import PairStdDev

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology ProbabilityTheory
namespace CubeSqrtPair

theorem linear_pair_variance_formula {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (d e : Ω → ℝ)
    (h2d : MemLp d 2 P) (h2e : MemLp e 2 P)
    (hd0 : ∫ w, d w ∂P = 0) (he0 : ∫ w, e w ∂P = 0) :
    Var[linearPair d e;P] =
      ((∫ w, (d w)^2 ∂P)+(∫ w, (e w)^2 ∂P)+2*cov[d,e;P])/4 := by
  have hLin : linearPair d e = fun w ↦ (1/2:ℝ)*(d w+e w) := by
    funext w; unfold linearPair; ring
  rw [hLin,variance_const_mul,variance_fun_add h2d h2e,
    variance_of_integral_eq_zero h2d.aemeasurable hd0,
    variance_of_integral_eq_zero h2e.aemeasurable he0]
  ring

theorem linear_pair_variance_lower {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (d e : Ω → ℝ)
    (h2d : MemLp d 2 P) (h2e : MemLp e 2 P)
    (hd0 : ∫ w, d w ∂P = 0) (he0 : ∫ w, e w ∂P = 0)
    (hCov : -Real.sqrt (∫ w, (d w)^2 ∂P) * Real.sqrt (∫ w, (e w)^2 ∂P)/2 ≤ cov[d,e;P]) :
    (∫ w, (d w)^2 ∂P)+(∫ w, (e w)^2 ∂P) ≤ 8*Var[linearPair d e;P] := by
  let A := ∫ w, (d w)^2 ∂P
  let B := ∫ w, (e w)^2 ∂P
  have hA : 0 ≤ A := integral_nonneg (fun _ ↦ sq_nonneg _)
  have hB : 0 ≤ B := integral_nonneg (fun _ ↦ sq_nonneg _)
  have h : 2*Real.sqrt A*Real.sqrt B ≤ A+B := by
    nlinarith only [sq_nonneg (Real.sqrt A-Real.sqrt B),Real.sq_sqrt hA,Real.sq_sqrt hB]
  rw [linear_pair_variance_formula P d e h2d h2e hd0 he0]
  change A+B ≤ 8*((A+B+2*cov[d,e;P])/4)
  change -Real.sqrt A*Real.sqrt B/2 ≤ cov[d,e;P] at hCov
  linarith only [h,hCov]

/-- Exact variance-stability sandwich for the tilted log-score. In particular
the relative factors tend to 1 as the original source amplitude tends to 0. -/
theorem actual_logPair_sqrt_variance_sandwich
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (d e : Ω → ℝ) (hmd : Measurable d) (hme : Measurable e)
    (a : ℝ) (ha0 : 0 ≤ a) (ha : a ≤ 1/2)
    (hd : ∀ w, |d w| ≤ a) (he : ∀ w, |e w| ≤ a)
    (hLinear : (∫ w, (d w)^2 ∂P)+(∫ w, (e w)^2 ∂P) ≤ 8*Var[linearPair d e;P]) :
    let s₀ := Real.sqrt (Var[linearPair d e;P])
    let sT := Real.sqrt (Var[logPair d e;P.tilted (logPair d e)])
    Real.sqrt ((1-a)/(1+a)) * ((1-4*a)*s₀) ≤ sT ∧
    sT ≤ Real.sqrt ((1+a)/(1-a)) * ((1+4*a)*s₀) := by
  dsimp only
  let V := logPair d e
  let T := linearPair d e
  let R : Ω → ℝ := fun w ↦ V w-T w
  let Q := P.tilted V
  have hVm : Measurable V := by unfold V logPair pairScore; fun_prop
  have hTm : Measurable T := by unfold T linearPair; fun_prop
  have hInt := logPair_density_ratio_bounds P d e hmd hme a ha hd he
  let _ : IsProbabilityMeasure Q := isProbabilityMeasure_tilted hInt.1
  have hB (w : Ω) : |V w| ≤ 2*a := logPair_abs_le_two_mul_amp d e a ha hd he w
  have hA (w : Ω) : |T w| ≤ a := by
    unfold T linearPair
    rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
    exact (div_le_iff₀ (by norm_num : (0:ℝ)<2)).2
      ((abs_add_le _ _).trans (by linarith only [hd w,he w]))
  have hV2P : MemLp V 2 P := MemLp.of_bound hVm.aestronglyMeasurable (2*a)
    (Eventually.of_forall fun w ↦ by simpa only [Real.norm_eq_abs] using hB w)
  have hV2Q : MemLp V 2 Q := MemLp.of_bound hVm.aestronglyMeasurable (2*a)
    (Eventually.of_forall fun w ↦ by simpa only [Real.norm_eq_abs] using hB w)
  have hT2 : MemLp T 2 P := MemLp.of_bound hTm.aestronglyMeasurable a
    (Eventually.of_forall fun w ↦ by simpa only [Real.norm_eq_abs] using hA w)
  have hR2 : MemLp R 2 P := hV2P.sub hT2
  have hd2 : MemLp d 2 P := MemLp.of_bound hmd.aestronglyMeasurable a
    (Eventually.of_forall fun w ↦ by simpa only [Real.norm_eq_abs] using hd w)
  have he2 : MemLp e 2 P := MemLp.of_bound hme.aestronglyMeasurable a
    (Eventually.of_forall fun w ↦ by simpa only [Real.norm_eq_abs] using he w)
  have hiD := (memLp_two_iff_integrable_sq hd2.aestronglyMeasurable).1 hd2
  have hiE := (memLp_two_iff_integrable_sq he2.aestronglyMeasurable).1 he2
  have hVarR : Var[R;P] ≤ (4*a)^2*Var[T;P] := by
    calc
      _ ≤ ∫ w, (R w)^2 ∂P := variance_le_expectation_sq hR2.aestronglyMeasurable
      _ ≤ ∫ w, (2*a^2)*((d w)^2+(e w)^2) ∂P :=
        integral_mono_of_nonneg (Eventually.of_forall fun w ↦ sq_nonneg (R w))
          ((hiD.add hiE).const_mul _) (Eventually.of_forall (logPair_linear_error_sq d e a ha hd he))
      _ = (2*a^2)*((∫ w, (d w)^2 ∂P)+(∫ w, (e w)^2 ∂P)) := by
        rw [integral_const_mul,integral_add hiD hiE]
      _ ≤ _ := by
        calc
          _ ≤ (2*a^2)*(8*Var[T;P]) := mul_le_mul_of_nonneg_left hLinear (by positivity)
          _ = _ := by ring
  have hSQ := Real.sqrt_le_sqrt hVarR
  rw [Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (by positivity : 0 ≤ 4*a)] at hSQ
  have hTri := (sqrt_variance_reverse_triangle P V T hV2P hT2).trans hSQ
  have hrLo : (1-4*a)*Real.sqrt (Var[T;P]) ≤ Real.sqrt (Var[V;P]) := by
    linarith only [(abs_le.mp hTri).1]
  have hrHi : Real.sqrt (Var[V;P]) ≤ (1+4*a)*Real.sqrt (Var[T;P]) := by
    linarith only [(abs_le.mp hTri).2]
  have haL : 0 ≤ (1-a)/(1+a) := div_nonneg (by linarith only [ha]) (by positivity)
  have haU : 0 ≤ (1+a)/(1-a) := div_nonneg (by positivity) (by linarith only [ha])
  obtain ⟨hlo,hhi⟩ := tilted_variance_sandwich P V V hVm hInt.1 hV2P hV2Q _ _ haL hInt.2
  have hL := Real.sqrt_le_sqrt hlo
  have hU := Real.sqrt_le_sqrt hhi
  rw [Real.sqrt_mul haL] at hL
  rw [Real.sqrt_mul haU] at hU
  exact ⟨(mul_le_mul_of_nonneg_left hrLo (Real.sqrt_nonneg _)).trans hL,
    hU.trans (mul_le_mul_of_nonneg_left hrHi (Real.sqrt_nonneg _))⟩

end CubeSqrtPair
#print axioms CubeSqrtPair.linear_pair_variance_lower
#print axioms CubeSqrtPair.actual_logPair_sqrt_variance_sandwich
