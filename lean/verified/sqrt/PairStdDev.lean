import TiltVarianceSandwich
import Mathlib.MeasureTheory.Function.L2Space
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal ProbabilityTheory RealInnerProductSpace
namespace CubeSqrtPair

theorem norm_centered_toLp
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P] (X : Ω → ℝ) (hX : MemLp X 2 P) :
    let c := ∫ w, X w ∂P
    let F (w : Ω) := X w-c
    let hF : MemLp F 2 P := hX.sub (memLp_const c)
    ‖hF.toLp F‖ = Real.sqrt (Var[X; P]) := by
  dsimp only
  let F (w : Ω) := X w-(∫ z, X z ∂P)
  have hF : MemLp F 2 P := hX.sub (memLp_const _)
  let A := hF.toLp F
  change ‖A‖ = Real.sqrt (Var[X;P])
  have hAE : (A : Ω → ℝ) =ᵐ[P] F := MemLp.coeFn_toLp hF
  have h : ‖A‖^2 = Var[X;P] := by
    rw [← real_inner_self_eq_norm_sq,MeasureTheory.L2.inner_def,variance_eq_integral hX.aemeasurable]
    apply integral_congr_ae
    filter_upwards [hAE] with w hw
    rw [hw,real_inner_self_eq_norm_sq,Real.norm_eq_abs,sq_abs]
  rw [← h,Real.sqrt_sq (norm_nonneg _)]

theorem sqrt_variance_reverse_triangle
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (hX : MemLp X 2 P) (hY : MemLp Y 2 P) :
    |Real.sqrt (Var[X;P])-Real.sqrt (Var[Y;P])| ≤
      Real.sqrt (Var[fun w ↦ X w-Y w;P]) := by
  let F (w : Ω) := X w-(∫ z, X z ∂P)
  let G (w : Ω) := Y w-(∫ z, Y z ∂P)
  let D (w : Ω) := X w-Y w
  let R (w : Ω) := D w-(∫ z, D z ∂P)
  have hF : MemLp F 2 P := hX.sub (memLp_const _)
  have hG : MemLp G 2 P := hY.sub (memLp_const _)
  have hD : MemLp D 2 P := hX.sub hY
  have hR : MemLp R 2 P := hD.sub (memLp_const _)
  let A := hF.toLp F
  let B := hG.toLp G
  let C := hR.toLp R
  have hAB : A-B=C := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_sub A B,MemLp.coeFn_toLp hF,MemLp.coeFn_toLp hG,
      MemLp.coeFn_toLp hR] with w hsub ha hb hc
    rw [hsub,Pi.sub_apply,ha,hb,hc]
    change X w-(∫ z, X z ∂P)-(Y w-(∫ z, Y z ∂P)) =
      (X w-Y w)-(∫ z, X z-Y z ∂P)
    rw [integral_sub (hX.integrable one_le_two) (hY.integrable one_le_two)]
    ring
  have ha : ‖A‖ = Real.sqrt (Var[X;P]) := norm_centered_toLp P X hX
  have hb : ‖B‖ = Real.sqrt (Var[Y;P]) := norm_centered_toLp P Y hY
  have hc : ‖C‖ = Real.sqrt (Var[D;P]) := norm_centered_toLp P D hD
  rw [← ha,← hb,show Real.sqrt (Var[fun w ↦ X w-Y w;P]) = ‖C‖ from hc.symm,← hAB]
  exact abs_norm_sub_norm_le _ _

end CubeSqrtPair
#print axioms CubeSqrtPair.sqrt_variance_reverse_triangle
