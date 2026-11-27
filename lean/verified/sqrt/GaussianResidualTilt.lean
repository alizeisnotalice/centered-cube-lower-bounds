import GaussianResidual
import GridAnchorTilt

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology ProbabilityTheory
namespace CubeBrownian

theorem gaussianReal_tilt_id_eq_shift (a : ℝ) (v : ℝ≥0) :
    (gaussianReal a v).tilted id = gaussianReal (a+(v:ℝ)) v := by
  let τ := gaussianReal 0 v
  let F : ℝ → ℝ := fun x ↦ x+a
  have hmF : Measurable F := by dsimp [F]; fun_prop
  have hF : τ.map F = gaussianReal a v := by
    simpa only [τ,F,zero_add] using (gaussianReal_map_add_const (μ:=0) (v:=v) a)
  have hFtilt : τ.tilted (id ∘ F) = τ.tilted id := by
    simpa only [F,Function.id_comp,sub_neg_eq_add,id_eq] using (tilt_sub_const τ id (-a))
  rw [← hF,← map_tilt_composition τ F id hmF measurable_id,hFtilt]
  have hc : τ.tilted id = gaussianReal v v := by
    change τ.tilted (fun x : ℝ ↦ x) = gaussianReal v v
    simpa only [τ,id_eq,one_mul] using gaussian_zero_tilt_eq_shift_all 1 v
  rw [hc]
  simpa only [F,add_comm] using (gaussianReal_map_add_const (μ:=(v:ℝ)) (v:=v) a)

theorem tilted_prod_fst_id
    {E : Type*} [MeasurableSpace E]
    (γ : Measure ℝ) [IsFiniteMeasure γ] (τ : Measure E) [IsProbabilityMeasure τ] :
    (γ.prod τ).tilted Prod.fst = (γ.tilted id).prod τ := by
  have hmgf : (∫ p : ℝ × E, Real.exp p.1 ∂(γ.prod τ)) = ∫ x : ℝ, Real.exp x ∂γ := by
    have h := integral_map
      (μ:=γ.prod τ) (φ:=Prod.fst) measurable_fst.aemeasurable Real.measurable_exp.aestronglyMeasurable
    rw [(measurePreserving_fst (μ:=γ) (ν:=τ)).map_eq] at h
    exact h.symm
  unfold Measure.tilted
  rw [hmgf,prod_withDensity_left]
  · rfl
  · fun_prop

/-- The exact Gaussian Esscher shift, proved from the independent scalar
regression residual without assuming nonsingular vector covariance. -/
theorem gaussian_tilt_difference_shift
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : Ω → ℝ) (D : Ω → E) (c : E)
    (hmZ : Measurable Z) (hmD : Measurable D)
    (hZD : HasGaussianLaw (fun w ↦ (Z w,D w)) μ)
    (hc : ∀ L : StrongDual ℝ E, cov[Z,L ∘ D; μ] = L c * Var[Z; μ])
    (a : ℝ) (v : ℝ≥0) (hZ : HasLaw Z (gaussianReal a v) μ) :
    (μ.tilted Z).map D = μ.map (fun w ↦ D w+(v:ℝ) • c) := by
  let R : Ω → E := fun w ↦ D w - Z w • c
  let τ := μ.map R
  let X : Ω → ℝ × E := fun w ↦ (Z w,R w)
  let X' : Ω → ℝ × E := fun w ↦ (Z w+(v:ℝ),R w)
  let T : ℝ × E → ℝ × E := Prod.map (fun x ↦ x+(v:ℝ)) id
  let F : ℝ × E → E := fun p ↦ p.2+p.1 • c
  have hmR : Measurable R := hmD.sub (hmZ.smul measurable_const)
  have hmX : Measurable X := hmZ.prodMk hmR
  have hmX' : Measurable X' := (hmZ.add_const _).prodMk hmR
  have hmT : Measurable T := by dsimp [T]; fun_prop
  have hmF : Measurable F := by dsimp [F]; fun_prop
  let _ : IsProbabilityMeasure τ := (Measure.isProbabilityMeasure_map_iff hmR.aemeasurable).2 inferInstance
  have hI : IndepFun Z R μ := gaussian_residual_indep μ Z D c hZD hc
  have hX : μ.map X = (gaussianReal a v).prod τ := by
    have H := hI.map_prod_eq_prod_map_map hmZ.aemeasurable hmR.aemeasurable
    rw [hZ.map_eq] at H
    exact H
  have hXt : (μ.tilted Z).map X = (gaussianReal (a+(v:ℝ)) v).prod τ := by
    change (μ.tilted (Prod.fst ∘ X)).map X = _
    rw [map_tilt_composition μ X Prod.fst hmX measurable_fst,hX,tilted_prod_fst_id,
      gaussianReal_tilt_id_eq_shift]
  have hX' : μ.map X' = (gaussianReal (a+(v:ℝ)) v).prod τ := by
    change μ.map (T ∘ X) = _
    rw [← Measure.map_map hmT hmX,hX]
    unfold T
    have hM : Measurable (fun x : ℝ ↦ x+(v:ℝ)) := by fun_prop
    rw [← Measure.map_prod_map _ _ hM measurable_id,
      gaussianReal_map_add_const,Measure.map_id]
  have hD : F ∘ X = D := by
    funext w
    simp [F,X,R]
  have hD' : F ∘ X' = fun w ↦ D w+(v:ℝ) • c := by
    funext w
    simp only [Function.comp_apply,F,X',R,add_smul]
    abel
  rw [← hD',← hD,← Measure.map_map hmF hmX,← Measure.map_map hmF hmX',hXt,hX']

end CubeBrownian
#print axioms CubeBrownian.gaussian_tilt_difference_shift
