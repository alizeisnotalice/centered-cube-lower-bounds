import GaussianWinner
import Mathlib.MeasureTheory.Function.L2Space
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
namespace CubeBrownian

theorem exp_abs_sub_le_mul (a b : ℝ) :
    |Real.exp a-Real.exp b| ≤ |a-b| * (Real.exp a+Real.exp b) := by
  wlog hab : b ≤ a generalizing a b
  · have h := this b a (le_of_not_ge hab)
    simpa only [abs_sub_comm,add_comm] using h
  have he := Real.add_one_le_exp (b-a)
  have h := mul_le_mul_of_nonneg_right he (Real.exp_pos a).le
  rw [← Real.exp_add,show b-a+a=b by ring] at h
  rw [abs_of_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr hab)),
    abs_of_nonneg (sub_nonneg.mpr hab)]
  calc
    Real.exp a-Real.exp b ≤ (a-b)*Real.exp a := by nlinarith only [h]
    _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (Real.exp_pos _).le) (sub_nonneg.mpr hab)

theorem exp_abs_sub_young (a b p : ℝ) (hp : 0 < p) :
    |Real.exp a-Real.exp b| ≤ p/2*(a-b)^2 + (Real.exp (2*a)+Real.exp (2*b))/p := by
  refine (exp_abs_sub_le_mul a b).trans ?_
  have hx := sq_nonneg (p*|a-b|-(Real.exp a+Real.exp b))
  have hy := sq_nonneg (Real.exp a-Real.exp b)
  have hA : |a-b|^2 = (a-b)^2 := sq_abs _
  have heA : Real.exp (2*a) = (Real.exp a)^2 := by rw [two_mul,Real.exp_add,pow_two]
  have heB : Real.exp (2*b) = (Real.exp b)^2 := by rw [two_mul,Real.exp_add,pow_two]
  rw [heA,heB,← hA]
  calc
    _ ≤ (p^2/2*|a-b|^2+((Real.exp a)^2+(Real.exp b)^2))/p := by
      apply (le_div_iff₀ hp).2
      nlinarith only [hx,hy]
    _ = _ := by field_simp

theorem finite_expMax_abs_sub_le_sum {ι : Type*} [Fintype ι] [Nonempty ι]
    (X Y : ι → ℝ) :
    |Real.exp (⨆ i, X i)-Real.exp (⨆ i, Y i)| ≤
      ∑ i, |Real.exp (X i)-Real.exp (Y i)| := by
  classical
  wlog h : (⨆ i, Y i) ≤ ⨆ i, X i generalizing X Y
  · have H := this Y X (le_of_not_ge h)
    simpa only [abs_sub_comm] using H
  obtain ⟨j,hj⟩ := exists_eq_ciSup_of_finite (f:=X)
  have hY := le_ciSup (finite_range Y).bddAbove j
  rw [abs_of_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr h)),← hj]
  calc
    Real.exp (X j)-Real.exp (⨆ i, Y i) ≤ Real.exp (X j)-Real.exp (Y j) :=
      sub_le_sub_left (Real.exp_le_exp.mpr hY) _
    _ ≤ |Real.exp (X j)-Real.exp (Y j)| := le_abs_self _
    _ ≤ _ := Finset.single_le_sum (f:=fun j ↦ |Real.exp (X j)-Real.exp (Y j)|)
      (fun _ _ ↦ abs_nonneg _) (Finset.mem_univ j)

theorem gaussian_half_variance_exp_second_moment {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {X : Ω → ℝ} {v : ℝ≥0}
    (hX : HasLaw X (gaussianReal (-(v:ℝ)/2) v) μ) :
    Integrable (fun w ↦ Real.exp (2*X w)) μ ∧
      (∫ w, Real.exp (2*X w) ∂μ) = Real.exp (v:ℝ) := by
  have he : Measurable (fun z : ℝ ↦ Real.exp (2*z)) := by fun_prop
  constructor
  · apply (integrable_map_measure he.aestronglyMeasurable hX.aemeasurable).mp
    rw [hX.map_eq]
    exact integrable_exp_mul_gaussianReal _
  · have h := integral_map hX.aemeasurable
      (he.aestronglyMeasurable : AEStronglyMeasurable (fun z : ℝ ↦ Real.exp (2*z)) (μ.map X))
    change (∫ z, Real.exp (2*z) ∂(μ.map X)) = ∫ w, Real.exp (2*X w) ∂μ at h
    rw [← h,hX.map_eq]
    change mgf (fun z : ℝ ↦ z) (gaussianReal (-(v:ℝ)/2) v) 2 = _
    rw [mgf_fun_id_gaussianReal]
    apply congrArg Real.exp
    ring

end CubeBrownian
#print axioms CubeBrownian.exp_abs_sub_young
#print axioms CubeBrownian.gaussian_half_variance_exp_second_moment
