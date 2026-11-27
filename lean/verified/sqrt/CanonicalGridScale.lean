import ActualFiniteSmoothing

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology RealInnerProductSpace
namespace CubeBrownian

set_option maxHeartbeats 850000
set_option linter.style.haveILetI false

theorem pairedIsoScore_scale_param {Ω H : Type*} [SeminormedAddCommGroup H] [NormedSpace ℝ H]
    (W : H →ₗ[ℝ] (Ω → ℝ)) (k : ℝ≥0) (x : H) (w : Ω) :
    isoScore W k x w=isoScore W 1 (Real.sqrt (k:ℝ) • x) w := by
  simp only [isoScore,isoVar,NNReal.coe_one,Real.sqrt_one,one_mul,map_smul,Pi.smul_apply,
    smul_eq_mul,NNReal.coe_mul,NNReal.coe_mk,norm_smul,pow_two,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg (k:ℝ))]
  rw [mul_mul_mul_comm (Real.sqrt (k:ℝ)) ‖x‖ (Real.sqrt (k:ℝ)) ‖x‖,
    show Real.sqrt (k:ℝ)*Real.sqrt (k:ℝ) = k by
    rw [← sq]; exact Real.sq_sqrt (NNReal.coe_nonneg _)]

theorem canonicalFiniteGridExp_scale {H I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [Fintype I] (f : I→H) (k : ℝ≥0) :
    canonicalFiniteGridExp f k=canonicalFiniteGridExp (fun i => Real.sqrt (k:ℝ) • f i) 1 := by
  let S := gridSpan f
  letI : MeasurableSpace S := borel _
  letI : BorelSpace S := ⟨rfl⟩
  let W := pairedSpanIsonormal S
  let μ := stdGaussian S
  let F (i : I) : S := Real.sqrt (k:ℝ) • gridSpanNode f i
  have hW (x:S) := pairedSpanIsonormal_hasLaw x
  have HH := finite_isonormal_expMax_eq_canonical μ W hW F
    (fun i => Real.sqrt (k:ℝ) • f i) (fun _ _ => rfl) 1
  change (∫ w, Real.exp (⨆ i, isoScore W k (gridSpanNode f i) w) ∂μ)=_
  simp_rw [pairedIsoScore_scale_param W k]
  exact HH

theorem canonicalFiniteGridExp_continuous_scale {H I : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [Fintype I] [Nonempty I] (f : I→H) :
    Continuous (canonicalFiniteGridExp f) := by
  refine continuous_iff_continuousAt.2 fun k => ?_
  apply Metric.tendsto_nhds.2
  intro ε hε
  have H (i : I) : Tendsto (fun a : ℝ≥0 => Real.sqrt (a:ℝ) • f i) (𝓝 k)
      (𝓝 (Real.sqrt (k:ℝ) • f i)) :=
    ((Real.continuous_sqrt.comp continuous_subtype_val).continuousAt.tendsto).smul_const _
  have W := canonical_finite_grid_uniform (fun (a : ℝ≥0) i => Real.sqrt (a:ℝ) • f i)
    (fun i => Real.sqrt (k:ℝ) • f i) H 1 ε hε
  filter_upwards [W] with a wa
  rw [Real.dist_eq,canonicalFiniteGridExp_scale f a,canonicalFiniteGridExp_scale f k]
  exact wa 1 le_rfl

#print axioms canonicalFiniteGridExp_continuous_scale
end CubeBrownian
