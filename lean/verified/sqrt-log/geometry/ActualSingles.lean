import ActualPairs

open MeasureTheory ProbabilityTheory Set

namespace CenteredCube.RudinDensity

noncomputable def singleLower : ℝ := CubeMD.mdLowerConstant / (2 * Real.exp (3/2))

noncomputable def singleUpper : ℝ := Real.exp 1 * CubeMD.mdUpperConstant

theorem mdLower_pos : 0 < CubeMD.mdLowerConstant := by
  unfold CubeMD.mdLowerConstant
  exact div_pos (gaussianPDFReal_pos 0 1 3 (by norm_num)) (by positivity)

theorem one_point_actual_bound {K n : ℕ} (hK : 4 ≤ K) (hn : 0 < n) {t u z : ℝ}
    (hu : 1 ≤ u) (hlow : u ≤ z) (hz2 : z^2 ≤ u^2+1) (hz' : z ≤ 2*u)
    (ht : |t - (K:ℝ)/4| ≤ (K:ℝ)/(100*u))
    (hN : readyMD n scoreB) (hWin : z^6 ≤ (n:ℝ))
    (hErr : 72*scoreB^3*z^3/Real.sqrt (n:ℝ) ≤ 1) :
    singleLower/u * Real.exp (-(u^2/2)) ≤
      (cellLaw n).real {v | z ≤ normalizedRow (normalizedScore K t) v} ∧
    (cellLaw n).real {v | z ≤ normalizedRow (normalizedScore K t) v} ≤
      singleUpper/u * Real.exp (-(u^2/2)) := by
  obtain ⟨hN0,hN1,hN2⟩ := hN
  have hu' : 3/50 ≤ u := by linarith
  have hu0 : 0 < u := by linarith
  have hz0 : 0 < z := hu0.trans_le hlow
  have hK1 : 1 ≤ K := by omega
  have hR : 0 < (K:ℝ)/8 := by
    have hk : (0:ℝ) < (K:ℝ) := by exact_mod_cast (show 0 < K by omega)
    positivity
  have hVt : 0 < VK K t := hR.trans_le (VK_window hK hu' ht).2.1
  have hb : 0 ≤ scoreB := by unfold scoreB; positivity
  have hPb : ∀ᵐ x ∂unitLaw, |normalizedScore K t x| ≤ scoreB :=
    Filter.Eventually.of_forall (by simpa only [scoreB] using normalizedScore_abs_le hK hu' ht)
  have hmd := CubeMD.iid_moderate_deviation (μ := unitLaw) (X := normalizedScore K t)
    n hn (normalizedScore_cont K t).measurable scoreB hb hPb
    (score_law_mean K hK1 t) (score_law_var K hK1 t hVt)
    hN0 hN1 hN2 z (hu.trans hlow) hWin
  let E : ℝ := 72*scoreB^3*z^3/Real.sqrt (n:ℝ)
  have hL : CubeMD.mdLowerConstant/z * Real.exp (-(z^2/2)-E) ≤
      (cellLaw n).real {v | z ≤ normalizedRow (normalizedScore K t) v} := hmd.1
  have hU : (cellLaw n).real {v | z ≤ normalizedRow (normalizedScore K t) v} ≤
      CubeMD.mdUpperConstant/z * Real.exp (-(z^2/2)+E) := hmd.2
  have hErr' : E ≤ 1 := hErr
  have hmono : u^2 ≤ z^2 := by gcongr
  constructor
  · apply le_trans _ hL
    have hp : CubeMD.mdLowerConstant/(2*u) ≤ CubeMD.mdLowerConstant/z :=
      div_le_div_of_nonneg_left mdLower_pos.le hz0 hz'
    have he : Real.exp (-(u^2/2)-3/2) ≤ Real.exp (-(z^2/2)-E) :=
      Real.exp_le_exp.mpr (by linarith only [hz2,hErr'])
    have hid : singleLower/u * Real.exp (-(u^2/2)) =
        CubeMD.mdLowerConstant/(2*u)*Real.exp (-(u^2/2)-3/2) := by
      unfold singleLower
      rw [show -(u^2/2)-3/2 = -(u^2/2)-(3/2) by ring, Real.exp_sub]
      ring
    rw [hid]
    exact mul_le_mul hp he (Real.exp_pos _).le (div_nonneg mdLower_pos.le hz0.le)
  · apply hU.trans
    have hp : CubeMD.mdUpperConstant/z ≤ CubeMD.mdUpperConstant/u :=
      div_le_div_of_nonneg_left mdUpper_nonneg hu0 hlow
    have he : Real.exp (-(z^2/2)+E) ≤ Real.exp (-(u^2/2)+1) :=
      Real.exp_le_exp.mpr (by linarith only [hmono,hErr'])
    have H := mul_le_mul hp he (Real.exp_pos _).le (div_nonneg mdUpper_nonneg hu0.le)
    exact H.trans_eq (by unfold singleUpper; rw [Real.exp_add]; ring)

end CenteredCube.RudinDensity

#print axioms CenteredCube.RudinDensity.one_point_actual_bound
