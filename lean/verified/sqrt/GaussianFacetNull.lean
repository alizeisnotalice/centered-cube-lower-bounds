import GaussianFacetSum

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ProbabilityTheory
namespace CubeSqrtProbability

/-- A genuine null linear relation from the finite facet Gram matrix
continues to hold almost surely after iid Gaussian replacement. -/
theorem gaussian_companion_sum_ae_opposite {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Matrix ι ι ℝ) (hS : S.PosSemidef) (i j : ι) (n : ℕ)
    (hnull : S i i + S i j + S j i + S j j=0) :
    ∀ᵐ x ∂sumLaw (centeredGaussianCompanion S) n, x i = -x j := by
  let ν := centeredGaussianCompanion S
  let L : (ι → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) i + ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) j
  have hl (x : ι → ℝ) : L x = x i+x j := rfl
  have hLp (a : ι) : MemLp (fun x : ι → ℝ ↦ x a) 2 ν :=
    IsGaussian.memLp_dual ν (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) a) 2 (by norm_num)
  have hI (a : ι) : Integrable (fun x : ι → ℝ ↦ x a) ν := (hLp a).integrable (by norm_num)
  have hm : (∫ x, L x ∂ν)=0 := by
    simp_rw [hl]
    rw [integral_add (hI i) (hI j),centeredGaussianCompanion_mean S hS,
      centeredGaussianCompanion_mean S hS,add_zero]
  have hII (a b : ι) : Integrable (fun x : ι → ℝ ↦ x a*x b) ν :=
    (hLp a).integrable_mul (hLp b)
  have hv : variance L ν=0 := by
    rw [variance_of_integral_eq_zero L.continuous.measurable.aemeasurable hm]
    simp_rw [hl,show ∀ a b : ℝ, (a+b)^2 = a*a+a*b+b*a+b*b by intros; ring]
    have e1 := integral_add (((hII i i).add (hII i j)).add (hII j i)) (hII j j)
    have e2 := integral_add ((hII i i).add (hII i j)) (hII j i)
    have e3 := integral_add (hII i i) (hII i j)
    simp only [Pi.add_apply] at e1 e2
    rw [e1,e2,e3]
    have hM (a b : ι) : (∫ x : ι → ℝ, x a*x b ∂ν) = S a b :=
      centeredGaussianCompanion_second_moment S hS a b
    rw [hM i i,hM i j,hM j i,hM j j]
    exact hnull
  have hG := gaussian_sumLaw_linear_marginal ν n L
  rw [hm,hv,mul_zero,Real.toNNReal_zero,smul_zero,gaussianReal_zero_var] at hG
  have hae : ∀ᵐ y ∂(sumLaw ν n).map L, y=(0:ℝ) := by rw [hG]; simp
  have hzero : ∀ᵐ x ∂sumLaw ν n, L x=0 :=
    (ae_map_iff L.continuous.measurable.aemeasurable (measurableSet_singleton (0:ℝ))).mp hae
  exact hzero.mono fun x hx ↦ by have h := hl x; linarith

end CubeSqrtProbability
#print axioms CubeSqrtProbability.gaussian_companion_sum_ae_opposite
