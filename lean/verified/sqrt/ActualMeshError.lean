import ActualWeightedMesh
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace CubeBrownian

theorem actual_weighted_grid_error {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B μ)
    (hmB : ∀ t, Measurable (B t)) (A : ℝ≥0) (hA : 0 < A)
    (N : ℕ) (hN : 0 < N) (b δ : ℝ) (hb : (A:ℝ) ≤ b) (hδ : 8*b ≤ δ) :
    let T := cellLeft A N
    let H := ∫ w, Real.exp (meshGridMax B A N w) ∂μ
    0 ≤ maxExpFormula (T:ℝ)-H ∧
    maxExpFormula (T:ℝ)-H ≤
      (1-Real.exp (-δ))*maxExpFormula (T:ℝ) +
      8*(N:ℝ)*((N:ℝ)+1)*Real.exp (δ-δ^2/(8*b)) := by
  dsimp only
  let T := cellLeft A N
  let M := driftedBrownianGridMax B T
  let G := meshGridMax B A N
  let U := meshModulus B A N
  let X (i : Fin (N+1)) := fun w ↦ driftedCentered B w (cellLeft A i)
  let H := ∫ w, Real.exp (G w) ∂μ
  let F := maxExpFormula (T:ℝ)
  let R := 8*(N:ℝ)*((N:ℝ)+1)*Real.exp (δ-δ^2/(8*b))
  have hT : 0 < T := by unfold T cellLeft; positivity
  have hT' : 0 < (T:ℝ) := by exact_mod_cast hT
  have hAr : 0 < (A:ℝ) := by exact_mod_cast hA
  have hbpos : 0 < b := hAr.trans_le hb
  have hdpos : 0 ≤ δ := by linarith only [hδ,hbpos]
  have hmf (t : ℝ≥0) : Measurable (fun w ↦ driftedCentered B w t) :=
    (measurable_const.mul ((hmB t).sub (hmB 0))).sub measurable_const
  have hmM : Measurable M := measurable_sampledSup _ (fun k ↦ hmf (gridSample T k))
  have hmG : Measurable G := measurable_meshGridMax B hmB A N
  have hmU : Measurable U := measurable_meshModulus B hmB A N hN
  have hmX (i : Fin (N+1)) : Measurable (X i) := hmf (cellLeft A i)
  have hAEP : ∀ᵐ w ∂μ, 0 ≤ M w ∧ G w ≤ M w ∧ M w ≤ G w+U w ∧ ∃ i, G w = X i w :=
    hB.cont.mono (fun w hw ↦ meshGrid_path_bounds B w hw A hA N hN)
  let _ : IsProbabilityMeasure μ := hB.toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
  have hTail : HasReflectedTail μ M (T:ℝ) := by
    intro x hx
    have h := driftedBrownianGridMax_ae_eq_pathSup μ hB T hT
    have he : {w | x < M w} =ᵐ[μ] {w | x < ⨆ t : Icc (0:ℝ≥0) T, Real.sqrt 2 * B t w - (t.1:ℝ)} := by
      filter_upwards [h] with w hw
      change M w = _ at hw
      simp only [hw]
    rw [measure_congr he]
    exact paperBrownian_reflected_tail_complete μ hB T hT x hx
  have hF : (∫⁻ w, ENNReal.ofReal (Real.exp (M w)) ∂μ) = ENNReal.ofReal F :=
    exp_expectation_of_reflected_tail μ M (T:ℝ) hT' hmM.aemeasurable
      (hAEP.mono (fun _ h ↦ h.1)) hTail
  let QG := ∫⁻ w, ENNReal.ofReal (Real.exp (G w)) ∂μ
  have hGle : QG ≤ ENNReal.ofReal F := by
    rw [← hF]
    apply lintegral_mono_ae
    exact hAEP.mono (fun w hw ↦ ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hw.2.1))
  have hGfin : QG ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hGle
  have hH : H = QG.toReal :=
    integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall (fun _ ↦ (Real.exp_pos _).le))
      (Real.measurable_exp.comp hmG).aestronglyMeasurable
  have hF0 : 0 ≤ F := by
    unfold F maxExpFormula
    exact add_nonneg (mul_nonneg (by linarith) (cdf_nonneg _ _))
      (mul_nonneg (Real.sqrt_nonneg _) (phi_bounded _).1)
  let C := 1-Real.exp (-δ)
  have hc0 : 0 ≤ C := sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hdpos))
  have hr0 : 0 ≤ R := by unfold R; positivity
  have hGap := weighted_grid_lintegral_bound μ M G U X hmM hmG hmU hmX δ hdpos
    (hAEP.mono (fun _ h ↦ h.2.2)) (fun i ↦ driftedCentered_exp_normalized μ hB.toIsPreBrownianReal _)
  have hR : (∑ i : Fin (N+1), ∫⁻ w in {w | δ < U w},
      ENNReal.ofReal (Real.exp (U w)) ∂(μ.tilted (X i))) ≤ ENNReal.ofReal R := by
    calc
      _ ≤ ∑ _ : Fin (N+1), 2*(4*(N:ℝ≥0∞))*ENNReal.ofReal (Real.exp (δ-δ^2/(8*b))) := by
        apply Finset.sum_le_sum
        intro i _
        exact weighted_modulus_exp_bound _ U hmU _ b δ hbpos hδ
          (fun x hx ↦ meshModulus_anchor_tail μ hB hmB A hA N hN i b x hb hx)
      _ = _ := by
        unfold R
        simp only [Finset.sum_const, Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_add,Nat.cast_one]
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_mul (by positivity)]
        simp only [ENNReal.ofReal_add (Nat.cast_nonneg N) zero_le_one, ENNReal.ofReal_natCast,
          ENNReal.ofReal_one, ENNReal.ofReal_ofNat]
        ring
  rw [hF] at hGap
  let E := ENNReal.ofReal C*ENNReal.ofReal F
  have hE : E ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hGE : QG+E ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨hGfin,hE⟩
  have hfin : QG+E+ENNReal.ofReal R ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨hGE,ENNReal.ofReal_ne_top⟩
  have hGap' : ENNReal.ofReal F ≤ QG+E+ENNReal.ofReal R :=
    hGap.trans (add_le_add_right hR _)
  have hReal := (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top hfin).mpr hGap'
  rw [ENNReal.toReal_add hGE ENNReal.ofReal_ne_top,ENNReal.toReal_add hGfin hE,← hH,
    ENNReal.toReal_ofReal hF0,ENNReal.toReal_ofReal hr0] at hReal
  have hEt : E.toReal = C*F := by rw [show E = ENNReal.ofReal C * ENNReal.ofReal F by rfl,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal hc0,ENNReal.toReal_ofReal hF0]
  rw [hEt] at hReal
  have hLow := (ENNReal.toReal_le_toReal hGfin ENNReal.ofReal_ne_top).mpr hGle
  rw [← hH,ENNReal.toReal_ofReal hF0] at hLow
  change 0 ≤ F-H ∧ F-H ≤ C*F+R
  exact ⟨sub_nonneg.mpr hLow,by linarith only [hReal]⟩

end CubeBrownian
#print axioms CubeBrownian.actual_weighted_grid_error
