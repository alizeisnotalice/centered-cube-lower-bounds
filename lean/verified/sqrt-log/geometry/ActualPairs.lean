import PointNumeric
import ModerateDeviation

open Set MeasureTheory ProbabilityTheory

namespace CenteredCube.RudinDensity

noncomputable def scoreB : ℝ := 5 * Real.sqrt 8

noncomputable def pairB (ε : ℝ) : ℝ := (2*scoreB) / Real.sqrt (2*ε)

def readyMD (n : ℕ) (b : ℝ) : Prop :=
  (32 * b ^ 3) ^ 3 ≤ (n : ℝ) ∧
  (4 * Real.sqrt 6 * (30 * 64 * b ^ 3) / gaussianPDFReal 0 1 3) ^ 3 ≤ (n : ℝ) ∧
  (30 * 64 * b ^ 3) ^ 3 ≤ (n : ℝ)

theorem mdUpper_nonneg : 0 ≤ CubeMD.mdUpperConstant := by
  unfold CubeMD.mdUpperConstant
  have hh : Real.exp (-1 : ℝ) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  exact div_nonneg (by positivity) (sub_nonneg.mpr hh.le)

theorem two_point_actual_bound {K n : ℕ} (hK : 4 ≤ K) (hn : 0 < n) {t s u ε : ℝ}
    (hu : 1 ≤ u) (hε : 0 < ε) (hκ : ε ≤ 1 + kappa K t s)
    (ht : |t - (K:ℝ)/4| ≤ (K:ℝ)/(100*u))
    (hs : |s - (K:ℝ)/4| ≤ (K:ℝ)/(100*u))
    (hN : readyMD n (pairB ε))
    (hWin : (2*u / Real.sqrt (2*ε))^6 ≤ (n:ℝ))
    (hErr : 72 * (pairB ε)^3 * (2*u / Real.sqrt (2*ε))^3 / Real.sqrt (n:ℝ) ≤ 1) :
    (cellLaw n).real
      ({v | u ≤ normalizedRow (normalizedScore K t) v} ∩
        {v | u ≤ normalizedRow (normalizedScore K s) v}) ≤
      (Real.exp 1*CubeMD.mdUpperConstant)/u * Real.exp (-(u^2)/(1+kappa K t s)) := by
  obtain ⟨hN0,hN1,hN2⟩ := hN
  have hu' : 3 / 50 ≤ u := by linarith
  have hU : 0 < u := by linarith
  have hK1 : 1 ≤ K := by omega
  have hR : 0 < (K:ℝ)/8 := by
    have hk : (0:ℝ) < (K:ℝ) := by exact_mod_cast (show 0 < K by omega)
    positivity
  have hVt : 0 < VK K t := hR.trans_le (VK_window hK hu' ht).2.1
  have hVs : 0 < VK K s := hR.trans_le (VK_window hK hu' hs).2.1
  have hκ0 : 0 < 1 + kappa K t s := hε.trans_le hκ
  have hκ1 := covariance_le_one K hK1 t s hVt hVs
  have hlow := pair_threshold_lower hU.le hκ0 hκ1
  have hhi := pair_threshold_upper hU.le hε hκ
  have h0 : 0 ≤ pairB ε := by unfold pairB scoreB; positivity
  have hWin' : (pairThreshold K t s u)^6 ≤ (n:ℝ) :=
    (pow_le_pow_left₀ (hU.le.trans hlow) hhi 6).trans hWin
  have he' : 72 * (pairB ε)^3 * (pairThreshold K t s u)^3 / Real.sqrt (n:ℝ) ≤ 1 := by
    apply le_trans _ hErr
    gcongr
    exact hU.le.trans hlow
  have hPb : ∀ᵐ x ∂unitLaw, |sumScore K t s x| ≤ pairB ε :=
    Filter.Eventually.of_forall (by simpa only [pairB, scoreB] using sumScore_abs_le hK hu' hε hκ ht hs)
  have hmd := CubeMD.iid_moderate_deviation (μ := unitLaw) (X := sumScore K t s)
    n hn (sumScore_measurable K t s) (pairB ε) h0 hPb
    (pair_law_mean K hK1 t s) (pair_law_var K hK1 t s hVt hVs hκ0)
    hN0 hN1 hN2 (pairThreshold K t s u) (hu.trans hlow) hWin'
  apply two_point_numeric hn hU mdUpper_nonneg he' hκ0 hκ1
  simpa only [cellLaw, normalizedRow, neg_div] using hmd.2

end CenteredCube.RudinDensity

#print axioms CenteredCube.RudinDensity.two_point_actual_bound
