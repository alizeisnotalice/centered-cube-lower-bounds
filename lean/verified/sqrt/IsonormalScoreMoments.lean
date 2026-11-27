import IsonormalBrownianLaw

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal ProbabilityTheory RealInnerProductSpace
namespace CubeBrownian

theorem isoScore_covariance
    {Ω H : Type*} [MeasurableSpace Ω] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : H →ₗ[ℝ] (Ω → ℝ))
    (hW : ∀ x, HasLaw (W x) (gaussianReal 0 (isoVar 1 x)) μ)
    (k : ℝ≥0) (x y : H) :
    cov[isoScore W k x,isoScore W k y;μ] = (k:ℝ)*⟪x,y⟫ := by
  let a := Real.sqrt (k:ℝ)
  have hm (z : H) : MemLp (W z) 2 μ := (hW z).memLp IsGaussian.memLp_two_id
  have hi (z : H) : Integrable (fun w ↦ a * W z w) μ := ((hm z).integrable one_le_two).const_mul a
  change cov[(fun w ↦ a*W x w - (isoVar k x:ℝ)/2),
    (fun w ↦ a*W y w - (isoVar k y:ℝ)/2);μ] = _
  simp only [sub_eq_add_neg]
  rw [covariance_add_const_left (hi x),covariance_add_const_right (hi y),
    covariance_const_mul_left,covariance_const_mul_right,isonormal_covariance μ W hW,
    ← mul_assoc,show a*a = (k:ℝ) by rw [← sq]; exact Real.sq_sqrt (NNReal.coe_nonneg _)]

theorem isoScore_finite_hasGaussianLaw
    {Ω H I : Type*} [MeasurableSpace Ω] [SeminormedAddCommGroup H] [NormedSpace ℝ H]
    [Fintype I] (μ : Measure Ω)
    (W : H →ₗ[ℝ] (Ω → ℝ))
    (hW : ∀ x, HasLaw (W x) (gaussianReal 0 (isoVar 1 x)) μ)
    (k : ℝ≥0) (f : I → H) :
    HasGaussianLaw (fun w i ↦ isoScore W k (f i) w) μ := by
  let X (w : Ω) (i : I) := W (Real.sqrt (k:ℝ) • f i) w
  let c : I → ℝ := fun i ↦ - (isoVar k (f i):ℝ)/2
  let T : (I → ℝ) → (I → ℝ) := fun y ↦ y+c
  have hX : HasGaussianLaw X μ := isonormal_finite_hasGaussianLaw μ W hW _
  have hT : Measurable T := by dsimp [T]; fun_prop
  have hScore : (fun w i ↦ isoScore W k (f i) w) = T ∘ X := by
    funext w i
    simp only [isoScore,Function.comp_apply,T,X,c,Pi.add_apply,map_smul,Pi.smul_apply,smul_eq_mul]
    ring
  rw [hScore]
  refine ⟨hT.aemeasurable.comp_aemeasurable hX.aemeasurable,?_⟩
  rw [← AEMeasurable.map_map_of_aemeasurable hT.aemeasurable hX.aemeasurable]
  let _ := hX.isGaussian_map
  dsimp only [T]
  infer_instance

end CubeBrownian
#print axioms CubeBrownian.isoScore_covariance
#print axioms CubeBrownian.isoScore_finite_hasGaussianLaw
