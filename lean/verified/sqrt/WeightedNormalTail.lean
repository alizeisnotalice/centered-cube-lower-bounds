import WeightedWinnerComparison
import ThinLayerLimit
import GaussianStrip
open MeasureTheory ProbabilityTheory Filter Set CubeBrownian CubeSqrtProbability
open scoped NNReal ENNReal Topology ProbabilityTheory
namespace CubeSqrtPair

theorem half_open_window_cdf_error (P Q : Measure ℝ) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (δ : ℝ) (h : ∀ x, |P.real (Iic x)-Q.real (Iic x)| ≤ δ) (a b : ℝ) (hab : a ≤ b) :
    |P.real (Ioc a b)-Q.real (Ioc a b)| ≤ 2*δ := by
  have he : Ioc a b = Iic b \ Iic a := by ext x; simp [and_comm,not_le]
  rw [he,measureReal_sdiff (Iic_subset_Iic.mpr hab) measurableSet_Iic,
    measureReal_sdiff (Iic_subset_Iic.mpr hab) measurableSet_Iic]
  rw [show P.real (Iic b)-P.real (Iic a)-(Q.real (Iic b)-Q.real (Iic a)) =
      (P.real (Iic b)-Q.real (Iic b))-(P.real (Iic a)-Q.real (Iic a)) by ring]
  exact (abs_sub _ _).trans (by linarith only [h a,h b])

theorem winnerWeight_const_univ_eq_tail
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (Z : Ω → ℝ) (hmZ : Measurable Z) :
    winnerFaceWeight μ Z (fun _ ↦ (0:ℝ)) univ =
      ∫ x in {x | 0 < Z x}, Real.exp (-(Z x)) ∂μ := by
  unfold winnerFaceWeight
  simp only [mem_univ,and_true]
  exact (integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall fun x ↦ (Real.exp_pos (-(Z x))).le)
    (Real.measurable_exp.comp hmZ.neg).aestronglyMeasurable).symm

theorem weighted_gaussian_shifted_tail_density (a : ℝ) (v : ℝ≥0) (hv : 0 < v) :
    winnerFaceWeight (gaussianReal a v) id (fun _ ↦ (0:ℝ)) univ =
      ∫ r in Ioi (0:ℝ), Real.exp (-r)*gaussianPDFReal a v r := by
  let τ := gaussianReal a v
  let R : ℝ → ℝ := fun _ ↦ 0
  have hInd : IndepFun (id : ℝ → ℝ) R τ := indepFun_const_right (μ:=τ) (id : ℝ → ℝ) (0:ℝ)
  have h := gaussian_face_weighted_kernel τ id R measurable_id measurable_const hInd a hv
    (HasLaw.id (μ:=τ)) univ MeasurableSet.univ
  let _ : IsProbabilityMeasure (τ.map R) :=
    (Measure.isProbabilityMeasure_map_iff measurable_const.aemeasurable).2 inferInstance
  have he (x : ℝ) : faceSectionProb (τ.map R) univ x = 1 := by
    simp [faceSectionProb]
  simpa only [winnerFaceWeight,mem_univ,and_true,he,mul_one] using h

theorem gaussian_density_weighted_le_peak (a : ℝ) (v : ℝ≥0) (hv : 0 < v) :
    (∫ r in Ioi (0:ℝ), Real.exp (-r)*gaussianPDFReal a v r) ≤ φ 0/Real.sqrt (v:ℝ) := by
  have hs : 0 < Real.sqrt (v:ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hv)
  have hPhi : φ 0 = (Real.sqrt (2*Real.pi))⁻¹ := by
    simp [φ,gaussianPDFReal_def]
  have hD (x : ℝ) : gaussianPDFReal a v x ≤ φ 0/Real.sqrt (v:ℝ) := by
    rw [gaussianPDFReal_eq_standardized _ _ hv,hPhi]
    exact div_le_div_of_nonneg_right (phi_bounded _).2 hs.le
  have hM : IntegrableOn (fun x ↦ Real.exp (-x)*(φ 0/Real.sqrt (v:ℝ))) (Ioi 0) :=
    (integrableOn_exp_neg_Ioi 0).mul_const _
  refine (integral_mono_of_nonneg (Eventually.of_forall fun x ↦
    mul_nonneg (Real.exp_pos _).le (gaussianPDFReal_nonneg _ _ _)) hM ?_).trans_eq ?_
  · exact Eventually.of_forall fun x ↦ mul_le_mul_of_nonneg_left (hD x) (Real.exp_pos _).le
  · rw [integral_mul_const,integral_exp_neg_Ioi_zero,one_mul]

/-- Both sides use the same threshold; the CDF assumption is on standardized
closed half-lines, but the exact tail has a strict lower and closed upper edge. -/
theorem weighted_tail_normal_comparison
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ) (hm : Measurable X)
    (M s h δ : ℝ) (hs : 0 < s)
    (hCDF : ∀ x, |(P.map (fun w ↦ (X w-M)/s)).real (Iic x) -
      (gaussianReal 0 1).real (Iic x)| ≤ δ) :
    (∫ w in {w | h < X w}, Real.exp (-(X w-h)) ∂P) ≤
      (∫ r in Ioi (0:ℝ), Real.exp (-r)*gaussianPDFReal (M-h) (NNReal.mk (s^2) (sq_nonneg _)) r) + 2*δ := by
  let U : Ω → ℝ := fun w ↦ (X w-M)/s
  let V : Ω → ℝ := fun w ↦ X w-h
  let v : ℝ≥0 := NNReal.mk (s^2) (sq_nonneg _)
  let T : ℝ → ℝ := fun y ↦ s*y+(M-h)
  let P' := P.map U
  let N := gaussianReal 0 1
  let G := gaussianReal (M-h) v
  have hv : 0 < v := by change 0 < s^2; positivity
  have hmU : Measurable U := (hm.sub_const M).div_const s
  have hmV : Measurable V := hm.sub_const h
  have hmT : Measurable T := by dsimp [T]; fun_prop
  let _ : IsProbabilityMeasure P' := (Measure.isProbabilityMeasure_map_iff hmU.aemeasurable).2 inferInstance
  have hG : N.map T = G := by
    have hN : HasLaw (id : ℝ→ℝ) N N := HasLaw.id
    have hs := gaussianReal_add_const (gaussianReal_const_mul hN s) (M-h)
    simpa only [T,G,v,N,id_eq,mul_zero,zero_add,mul_one] using hs.map_eq
  have hTU : (fun w ↦ T (U w)) = V := by
    funext w
    dsimp [T,U,V]
    field_simp [hs.ne']
    ring
  have hWindow (r : ℝ) (hr : 0 < r) :
      |P.real (weightedWindow V 0 r ∩ (fun _ ↦ (0:ℝ)) ⁻¹' univ) -
        G.real (weightedWindow id 0 r ∩ (fun _ ↦ (0:ℝ)) ⁻¹' univ)| ≤ 2*δ := by
    simp only [preimage_univ,inter_univ]
    let a := (h-M)/s
    let b := (h+r-M)/s
    have hab : a ≤ b := by
      change (h-M)/s ≤ (h+r-M)/s
      apply div_le_div_of_nonneg_right _ hs.le
      linarith only [hr]
    have he : T ⁻¹' weightedWindow id 0 r = Ioc a b := by
      ext y
      change (0 < s*y+(M-h) ∧ s*y+(M-h) ≤ 0+r) ↔ ((h-M)/s < y ∧ y ≤ (h+r-M)/s)
      rw [div_lt_iff₀ hs,le_div_iff₀ hs]
      constructor <;> intro H <;> constructor <;> nlinarith only [H.1,H.2]
    have hP : P.real (weightedWindow V 0 r) = P'.real (Ioc a b) := by
      rw [Measure.real,Measure.real,Measure.map_apply hmU measurableSet_Ioc,← he,preimage_preimage,hTU]
      rfl
    have hG' : G.real (weightedWindow id 0 r) = N.real (Ioc a b) := by
      rw [← hG,Measure.real,Measure.real,Measure.map_apply hmT (weightedWindow_measurable measurable_id _ _),he]
    rw [hP,hG']
    exact half_open_window_cdf_error P' N δ hCDF a b hab
  have hComp := weighted_winner_face_comparison P G V (fun _ ↦ (0:ℝ)) id (fun _ ↦ (0:ℝ))
    hmV measurable_const measurable_id measurable_const univ univ MeasurableSet.univ MeasurableSet.univ (2*δ) hWindow
  rw [winnerWeight_const_univ_eq_tail P V hmV,weighted_gaussian_shifted_tail_density _ _ hv] at hComp
  have hSet : {w | 0 < V w} = {w | h < X w} := by
    ext w
    change (0 < X w-h) ↔ h < X w
    exact sub_pos
  rw [hSet] at hComp
  have hh := (abs_le.mp hComp).2
  exact (sub_le_iff_le_add.mp hh).trans_eq (add_comm _ _)

end CubeSqrtPair
#print axioms CubeSqrtPair.weighted_tail_normal_comparison
#print axioms CubeSqrtPair.gaussian_density_weighted_le_peak
