import CanonicalPreBrownian
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology BigOperators

namespace CubeBrownian

noncomputable def stdBrownianFourth : ℝ := ∫ x : ℝ, |x|^4 ∂(gaussianReal 0 1)

theorem stdBrownianFourth_nonneg : 0 ≤ stdBrownianFourth :=
  integral_nonneg (fun _ => pow_nonneg (abs_nonneg _) _)

theorem gaussian_abs_fourth (v : ℝ≥0) :
    (∫ x : ℝ, |x|^4 ∂(gaussianReal 0 v)) = stdBrownianFourth*(v:ℝ)^2 := by
  let s := √(v:ℝ)
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : NNReal.mk (s^2) (sq_nonneg s) = v :=
    NNReal.eq (Real.sq_sqrt v.coe_nonneg)
  have hm := gaussianReal_map_const_mul (μ := 0) (v := 1) s
  rw [mul_zero,mul_one,hs2] at hm
  rw [← hm,integral_map (by fun_prop) (by fun_prop)]
  simp_rw [abs_mul, abs_of_nonneg hs, mul_pow, integral_const_mul, stdBrownianFourth]
  have hh : s^4 = (v:ℝ)^2 := by rw [show s^4 = (s^2)^2 by ring]; simp [s,v.coe_nonneg]
  rw [hh]
  ring

theorem preBrownian_increment_abs_fourth {Ω : Type*} [MeasurableSpace Ω]
    {B : ℝ≥0 → Ω → ℝ} {μ : Measure Ω} (hB : IsPreBrownianReal B μ) (s t : ℝ≥0) :
    Integrable (fun ω => |B s ω - B t ω|^4) μ ∧
      (∫ ω, |B s ω-B t ω|^4 ∂μ) = stdBrownianFourth*|(s:ℝ)-(t:ℝ)|^2 := by
  let v := nndist (s:ℝ) (t:ℝ)
  have hG : Integrable (fun x : ℝ => |x|^4) (gaussianReal 0 v) := by
    simpa only [id_eq, Real.norm_eq_abs] using
      (memLp_id_gaussianReal (μ := 0) (v := v) 4).integrable_norm_pow' (p := 4)
  have hl := hB.hasLaw_sub s t
  change HasLaw (fun ω => B s ω - B t ω) (gaussianReal 0 v) μ at hl
  have hme := (continuous_abs.pow 4).aestronglyMeasurable (μ := gaussianReal 0 v)
  have hh : Integrable (fun ω => |B s ω - B t ω|^4) μ := by
    have hG' := hG
    rw [← hl.map_eq] at hG' hme
    exact (integrable_map_measure hme hl.aemeasurable).mp hG'
  refine ⟨hh,?_⟩
  calc
    _ = ∫ x : ℝ, |x|^4 ∂(gaussianReal 0 v) := by
      rw [← hl.map_eq]
      exact (integral_map hl.aemeasurable (continuous_abs.pow 4).aestronglyMeasurable).symm
    _ = _ := by rw [gaussian_abs_fourth]; simp [v, Real.dist_eq]

theorem preBrownian_increment_tail {Ω : Type*} [MeasurableSpace Ω]
    {B : ℝ≥0 → Ω → ℝ} {μ : Measure Ω} (hB : IsPreBrownianReal B μ) (s t : ℝ≥0)
    {r : ℝ} (hr : 0 < r) :
    μ {ω | r < |B s ω-B t ω|} ≤
      ENNReal.ofReal (stdBrownianFourth * |(s:ℝ)-(t:ℝ)|^2 / r^4) := by
  let F : Ω → ℝ := fun ω => |B s ω-B t ω|^4
  let a := ENNReal.ofReal (r^4)
  have ha0 : a ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr (pow_pos hr _))
  have hat : a ≠ ⊤ := ENNReal.ofReal_ne_top
  obtain ⟨hi,hI⟩ := preBrownian_increment_abs_fourth hB s t
  have hM : AEMeasurable (fun ω => ENNReal.ofReal (F ω)) μ :=
    hi.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hsub : {ω | r < |B s ω-B t ω|} ⊆ {ω | a ≤ ENNReal.ofReal (F ω)} := by
    intro ω hω
    exact ENNReal.ofReal_le_ofReal
      (pow_le_pow_left₀ hr.le (show r ≤ |B s ω - B t ω| from hω.le) 4)
  have hU := mul_meas_ge_le_lintegral₀ hM a
  have h := (mul_le_mul_of_nonneg_left (measure_mono hsub) (show 0 ≤ a from bot_le)).trans hU
  have hNN : 0 ≤ᵐ[μ] F := Eventually.of_forall (fun ω => pow_nonneg (abs_nonneg _) _)
  have ho := ofReal_integral_eq_lintegral_ofReal hi hNN
  rw [← ho, hI] at h
  rw [ENNReal.ofReal_div_of_pos (pow_pos hr _)]
  exact (ENNReal.le_div_iff_mul_le (Or.inl ha0) (Or.inl hat)).2 (by simpa [mul_comm] using h)

#print axioms preBrownian_increment_abs_fourth
#print axioms preBrownian_increment_tail
end CubeBrownian
