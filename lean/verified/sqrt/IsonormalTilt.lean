import IsonormalBrownianLaw
import GaussianResidualTilt

open MeasureTheory ProbabilityTheory Finset
open scoped NNReal ENNReal ProbabilityTheory RealInnerProductSpace
namespace CubeBrownian

lemma real_dual_finite_pi_expand
    {I : Type*} [Fintype I] [DecidableEq I] (L : StrongDual ℝ (I → ℝ)) (v : I → ℝ) :
    L v = ∑ i, v i * L (Pi.single i 1) := by
  classical
  conv_lhs => rw [← Finset.univ_sum_single v]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [show Pi.single i (v i) = v i • Pi.single i (1:ℝ) from by
    ext j
    by_cases h : j = i <;> simp [h]]
  rw [map_smul]
  rfl

/-- Exponential tilting by one isonormal coordinate shifts the finite vector
by the corresponding Gram row, including when the Gram matrix is singular. -/
theorem isonormal_tilt_finite_gram_shift
    {Ω H I : Type*} [MeasurableSpace Ω] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [Fintype I] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : H →ₗ[ℝ] (Ω → ℝ)) (hmW : ∀ x, Measurable (W x))
    (hW : ∀ x, HasLaw (W x) (gaussianReal 0 (isoVar 1 x)) μ)
    (x : H) (f : I → H) :
    (μ.tilted (W x)).map (fun w i ↦ W (f i) w) =
      μ.map (fun w i ↦ W (f i) w + ⟪x,f i⟫) := by
  classical
  let Z := W x
  let D : Ω → I → ℝ := fun w i ↦ W (f i) w
  let G : I → ℝ := fun i ↦ ⟪x,f i⟫
  let v := isoVar 1 x
  let c : I → ℝ := (‖x‖^2)⁻¹ • G
  have hZ : Measurable Z := hmW x
  have hD : Measurable D := Measurable.of_eval (fun i ↦ hmW (f i))
  let f' : Option I → H := fun i ↦ i.elim x f
  let L₁ : (Option I → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj none
  let L₂ : (Option I → ℝ) →L[ℝ] (I → ℝ) :=
    ContinuousLinearMap.pi fun i ↦ ContinuousLinearMap.proj (some i)
  have hGaus : HasGaussianLaw (fun w ↦ (Z w,D w)) μ :=
    (isonormal_finite_hasGaussianLaw μ W hW f').map_fun (L₁.prod L₂)
  have hVar : Var[Z; μ] = (v:ℝ) := by
    have hh := (hW x).variance_eq
    change Var[Z; μ] = Var[fun y : ℝ ↦ y; gaussianReal 0 v] at hh
    rwa [variance_fun_id_gaussianReal] at hh
  have hvCo : (v:ℝ) = ‖x‖^2 := by simp [v,isoVar]
  have hvc : (v:ℝ) • c = G := by
    by_cases hx : x = 0
    · subst x
      ext i
      simp [v,c,G,isoVar]
    · have hn : ‖x‖^2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hx)
      rw [hvCo,show c = (‖x‖^2)⁻¹ • G by rfl,smul_smul,mul_inv_cancel₀ hn,one_smul]
  have hCov (L : StrongDual ℝ (I → ℝ)) : cov[Z,L ∘ D;μ] = L c * Var[Z;μ] := by
    let z := ∑ i, L (Pi.single i 1) • f i
    have hz : L ∘ D = W z := by
      funext w
      change L (D w) = W z w
      rw [real_dual_finite_pi_expand]
      simp only [D,z,map_sum,map_smul,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,mul_comm]
    have hLc : L G = L c * (v:ℝ) := by
      rw [← hvc,map_smul,smul_eq_mul,mul_comm (v:ℝ)]
    rw [hz,isonormal_covariance μ W hW,hVar,← hLc]
    rw [real_dual_finite_pi_expand,show z = ∑ i, L (Pi.single i 1) • f i from rfl,inner_sum]
    simp only [real_inner_smul_right,G,mul_comm]
  have H := gaussian_tilt_difference_shift μ Z D c hZ hD hGaus hCov 0 v (hW x)
  rw [hvc] at H
  exact H

/-- The Gaussian winner's own normalized exponential tilt shifts all
differences to exactly the normalized isonormal scores of translated nodes. -/
theorem isoScore_tilt_difference_law
    {Ω H I : Type*} [MeasurableSpace Ω] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [Fintype I] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : H →ₗ[ℝ] (Ω → ℝ)) (hmW : ∀ x, Measurable (W x))
    (hW : ∀ x, HasLaw (W x) (gaussianReal 0 (isoVar 1 x)) μ)
    (k : ℝ≥0) (f : I → H) (j : I) :
    (μ.tilted (isoScore W k (f j))).map
      (fun w i ↦ isoScore W k (f i) w-isoScore W k (f j) w) =
    μ.map (fun w i ↦ isoScore W k (f i-f j) w) := by
  let a := Real.sqrt (k:ℝ)
  let x := a • f j
  let g (i : I) := a • (f i-f j)
  let F : (I → ℝ) → (I → ℝ) := fun z i ↦ z i-((isoVar k (f i):ℝ)-(isoVar k (f j):ℝ))/2
  let X : Ω → I → ℝ := fun w i ↦ W (g i) w
  let X' : Ω → I → ℝ := fun w i ↦ W (g i) w+⟪x,g i⟫
  have hQ : μ.tilted (isoScore W k (f j)) = μ.tilted (W x) := by
    have hWB : W x = fun w ↦ a * W (f j) w := by
      simp only [x,map_smul,Pi.smul_apply,smul_eq_mul]
      rfl
    have hS : isoScore W k (f j) = fun w ↦ W x w-((isoVar k (f j):ℝ)/2) := by
      rw [hWB]
      rfl
    rw [hS,tilt_sub_const]
  have hmF : Measurable F := Measurable.of_eval fun i ↦ (measurable_pi_apply i).sub_const _
  have hmX : Measurable X := Measurable.of_eval fun i ↦ hmW (g i)
  have hmX' : Measurable X' := Measurable.of_eval fun i ↦ (hmW (g i)).add_const _
  have hX : (μ.tilted (W x)).map X = μ.map X' :=
    isonormal_tilt_finite_gram_shift μ W hmW hW x g
  have hFX : (fun w i ↦ isoScore W k (f i) w-isoScore W k (f j) w) = F ∘ X := by
    funext w i
    simp only [isoScore,F,Function.comp_apply,X,g,map_smul,Pi.smul_apply,smul_eq_mul,map_sub,
      Pi.sub_apply,a]
    ring
  have hFX' : (fun w i ↦ isoScore W k (f i-f j) w) = F ∘ X' := by
    funext w i
    simp only [isoScore,F,Function.comp_apply,X',g,x,map_smul,Pi.smul_apply,smul_eq_mul,
      real_inner_smul_left,real_inner_smul_right]
    rw [← mul_assoc a a,show a*a = (k:ℝ) by
      rw [← sq]; exact Real.sq_sqrt (NNReal.coe_nonneg _)]
    simp only [isoVar,NNReal.coe_mul,NNReal.coe_mk]
    rw [norm_sub_sq_real,inner_sub_right,real_inner_self_eq_norm_sq,real_inner_comm (f i) (f j)]
    dsimp only [a]
    ring
  rw [hQ,hFX,hFX',← Measure.map_map hmF hmX,← Measure.map_map hmF hmX',hX]

end CubeBrownian
#print axioms CubeBrownian.isonormal_tilt_finite_gram_shift
#print axioms CubeBrownian.isoScore_tilt_difference_law
