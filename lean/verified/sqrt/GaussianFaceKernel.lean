import ThinLayerLimit
import GaussianResidual
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.Prod
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology ProbabilityTheory
namespace CubeBrownian

noncomputable def faceSectionProb {E : Type*} [MeasurableSpace E]
    (τ : Measure E) (A : Set (ℝ × E)) (x : ℝ) : ℝ :=
  (τ ((fun y ↦ (x,y)) ⁻¹' A)).toReal

theorem measurable_faceSectionProb {E : Type*} [MeasurableSpace E]
    (τ : Measure E) [IsFiniteMeasure τ] {A : Set (ℝ × E)} (hA : MeasurableSet A) :
    Measurable (faceSectionProb τ A) :=
  (measurable_measure_prodMk_left (ν:=τ) hA).ennreal_toReal

theorem faceSectionProb_mem_Icc {E : Type*} [MeasurableSpace E]
    (τ : Measure E) [IsProbabilityMeasure τ] (A : Set (ℝ × E)) (x : ℝ) :
    faceSectionProb τ A x ∈ Icc (0:ℝ) 1 := by
  exact ⟨ENNReal.toReal_nonneg, by
    simpa only [faceSectionProb, ENNReal.toReal_one] using
      (ENNReal.toReal_mono ENNReal.one_ne_top (prob_le_one (μ:=τ) (s:=(fun y ↦ (x,y)) ⁻¹' A)))⟩

/-- Thin-layer disintegration using an independent residual vector. The result
uses only the nonzero scalar baseline variance, not an inverse residual covariance. -/
theorem gaussian_face_weighted_kernel {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : Ω → ℝ) (R : Ω → E)
    (hmZ : Measurable Z) (hmR : Measurable R)
    (hInd : IndepFun Z R μ) (a : ℝ) {v : ℝ≥0} (hv : 0 < v)
    (hZ : HasLaw Z (gaussianReal a v) μ) (A : Set (ℝ × E)) (hA : MeasurableSet A) :
    (∫⁻ w in {w | 0 < Z w ∧ (Z w,R w) ∈ A}, ENNReal.ofReal (Real.exp (-(Z w))) ∂μ).toReal =
    ∫ x in Ioi (0:ℝ), Real.exp (-x)*gaussianPDFReal a v x*faceSectionProb (μ.map R) A x := by
  let τ := μ.map R
  let G := gaussianReal a v
  let D : Ω → ℝ × E := fun w ↦ (Z w,R w)
  let S : Set (ℝ×E) := (Prod.fst ⁻¹' Ioi (0:ℝ)) ∩ A
  let H (x : ℝ) := ENNReal.ofReal (Real.exp (-x))
  let J (p : ℝ × E) := S.indicator (fun q ↦ H q.1) p
  have hmS : MeasurableSet S := (measurable_fst measurableSet_Ioi).inter hA
  have hmD : Measurable D := hmZ.prodMk hmR
  have hmH : Measurable H := by dsimp [H]; fun_prop
  have hmJ : Measurable J := (hmH.comp measurable_fst).indicator hmS
  let _ : IsProbabilityMeasure τ := (Measure.isProbabilityMeasure_map_iff hmR.aemeasurable).2 inferInstance
  have hDlaw : μ.map D = G.prod τ := by
    have h := hInd.map_prod_eq_prod_map_map hmZ.aemeasurable hmR.aemeasurable
    rw [hZ.map_eq] at h
    exact h
  have hS_pre : D ⁻¹' S = {w | 0 < Z w ∧ (Z w,R w) ∈ A} := rfl
  have hProd : (∫⁻ w, J (D w) ∂μ) = ∫⁻ p, J p ∂(G.prod τ) := by
    rw [← hDlaw,lintegral_map hmJ hmD]
  have hInner (x : ℝ) : (∫⁻ y, J (x,y) ∂τ) =
      (Ioi (0:ℝ)).indicator (fun x ↦ H x * τ ((fun y ↦ (x,y)) ⁻¹' A)) x := by
    by_cases hx : x ∈ Ioi (0:ℝ)
    · let E := (fun y ↦ (x,y)) ⁻¹' A
      have hE : MeasurableSet E := (measurable_const.prodMk measurable_id) hA
      have he : (fun y ↦ J (x,y)) = E.indicator (fun _ ↦ H x) := by
        funext y
        by_cases hy : y ∈ E
        · exact (indicator_of_mem (show (x,y) ∈ S from ⟨hx,hy⟩) _).trans
            (indicator_of_mem hy (fun _ ↦ H x)).symm
        · exact (indicator_of_notMem (show (x,y) ∉ S from fun h ↦ hy h.2) _).trans
            (indicator_of_notMem hy _).symm
      rw [he,lintegral_indicator hE,indicator_of_mem hx,lintegral_const,
        Measure.restrict_apply MeasurableSet.univ,univ_inter]
    · have he : (fun y ↦ J (x,y)) = 0 := by
        funext y
        exact indicator_of_notMem (show (x,y) ∉ S from fun h ↦ hx h.1) _
      rw [he,indicator_of_notMem hx,lintegral_zero_fun]
  have hProd' : (∫⁻ p, J p ∂(G.prod τ)) =
      ∫⁻ x in Ioi (0:ℝ), H x * τ ((fun y ↦ (x,y)) ⁻¹' A) ∂G := by
    rw [lintegral_prod _ hmJ.aemeasurable]
    simp_rw [hInner]
    rw [lintegral_indicator measurableSet_Ioi]
  have hSection (x : ℝ) : τ ((fun y ↦ (x,y)) ⁻¹' A) = ENNReal.ofReal (faceSectionProb τ A x) :=
    (ENNReal.ofReal_toReal (measure_ne_top τ _)).symm
  have hMeas : Measurable (fun x ↦ H x * τ ((fun y ↦ (x,y)) ⁻¹' A)) :=
    hmH.mul (measurable_measure_prodMk_left hA)
  have hDensity : (∫⁻ x in Ioi (0:ℝ), H x * τ ((fun y ↦ (x,y)) ⁻¹' A) ∂G) =
      ∫⁻ x in Ioi (0:ℝ), ENNReal.ofReal
        (Real.exp (-x)*gaussianPDFReal a v x*faceSectionProb τ A x) := by
    rw [show G = volume.withDensity (gaussianPDF a v) from gaussianReal_of_var_ne_zero _ hv.ne',
      setLIntegral_withDensity_eq_setLIntegral_mul _ (measurable_gaussianPDF _ _) hMeas measurableSet_Ioi]
    apply lintegral_congr
    intro x
    rw [Pi.mul_apply,gaussianPDF_def,hSection]
    dsimp only [H]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _)]
    congr 1
    ring
  have hStart : (∫⁻ w in {w | 0 < Z w ∧ (Z w,R w) ∈ A}, ENNReal.ofReal (Real.exp (-(Z w))) ∂μ) =
      ∫⁻ w, J (D w) ∂μ := by
    rw [← hS_pre,← lintegral_indicator (hmD hmS)]
    apply lintegral_congr
    intro w
    by_cases hw : w ∈ D ⁻¹' S
    · have hDw : D w ∈ S := hw
      simp only [J,H,indicator_of_mem hw,indicator_of_mem hDw,D]
    · have hDw : D w ∉ S := hw
      simp only [J,indicator_of_notMem hw,indicator_of_notMem hDw]
  rw [hStart,hProd,hProd',hDensity]
  symm
  exact integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x ↦ by
      exact mul_nonneg (mul_nonneg (Real.exp_pos _).le (gaussianPDFReal_nonneg _ _ _))
        (faceSectionProb_mem_Icc τ A x).1)
    (((Real.measurable_exp.comp measurable_neg).mul (measurable_gaussianPDFReal _ _)).mul
      (measurable_faceSectionProb τ hA)).aestronglyMeasurable
/-- The weighted face probability for the original score and difference vector
is an exact integral whose only conditioning variable is a scalar. -/
theorem gaussian_weighted_original_face
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : Ω → ℝ) (D : Ω → E) (c : E)
    (hmZ : Measurable Z) (hmD : Measurable D)
    (hZD : HasGaussianLaw (fun w ↦ (Z w,D w)) μ)
    (hc : ∀ L : StrongDual ℝ E, cov[Z, L ∘ D; μ] = L c * Var[Z; μ])
    (a : ℝ) {v : ℝ≥0} (hv : 0 < v) (hZ : HasLaw Z (gaussianReal a v) μ)
    (F : Set E) (hF : MeasurableSet F) :
    let R := fun w ↦ D w-Z w • c
    let A := {p : ℝ × E | p.2+p.1 • c ∈ F}
    (∫⁻ w in {w | 0 < Z w ∧ D w ∈ F}, ENNReal.ofReal (Real.exp (-(Z w))) ∂μ).toReal =
    ∫ x in Ioi (0:ℝ), Real.exp (-x)*gaussianPDFReal a v x*faceSectionProb (μ.map R) A x := by
  dsimp only
  let R := fun w ↦ D w-Z w • c
  let A := {p : ℝ × E | p.2+p.1 • c ∈ F}
  have hmR : Measurable R := hmD.sub (hmZ.smul measurable_const)
  have hA : MeasurableSet A :=
    (measurable_snd.add (measurable_fst.smul measurable_const)) hF
  have hEq : {w | 0 < Z w ∧ (Z w,R w) ∈ A} = {w | 0 < Z w ∧ D w ∈ F} := by
    ext w
    simp [A,R]
  have H := gaussian_face_weighted_kernel μ Z R hmZ hmR
    (gaussian_residual_indep μ Z D c hZD hc) a hv hZ A hA
  rw [hEq] at H
  exact H

end CubeBrownian
#print axioms CubeBrownian.gaussian_face_weighted_kernel
#print axioms CubeBrownian.gaussian_weighted_original_face
