import ExpMaxCoupling
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
namespace CubeBrownian

theorem integrable_exp_fin_sup {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [Nonempty ι]
    (μ : Measure Ω) (X : ι → Ω → ℝ) (hm : ∀ i, Measurable (X i))
    (hInt : ∀ i, Integrable (fun w ↦ Real.exp (X i w)) μ) :
    Integrable (fun w ↦ Real.exp (⨆ i, X i w)) μ := by
  classical
  have hMeas : Measurable (fun w ↦ ⨆ i, X i w) := by
    apply measurable_of_Ioi
    intro a
    have he : (fun w ↦ ⨆ i, X i w) ⁻¹' Ioi a = ⋃ i, {w | a < X i w} := by
      ext w
      change (a < ⨆ i, X i w) ↔ _
      rw [lt_ciSup_iff (finite_range (fun i ↦ X i w)).bddAbove]
      simp
    rw [he]
    exact MeasurableSet.iUnion (fun i ↦ measurableSet_lt measurable_const (hm i))
  have hSum : Integrable (fun w ↦ ∑ i, Real.exp (X i w)) μ :=
    integrable_finsetSum _ (fun i _ ↦ hInt i)
  apply hSum.mono' (Real.measurable_exp.comp hMeas).aestronglyMeasurable
  exact Eventually.of_forall (fun w ↦ by
    change ‖Real.exp (⨆ i, X i w)‖ ≤ _
    rw [Real.norm_eq_abs,abs_of_nonneg (Real.exp_pos _).le]
    obtain ⟨j,hj⟩ := exists_eq_ciSup_of_finite (f:=fun i ↦ X i w)
    rw [← hj]
    exact Finset.single_le_sum (f:=fun i ↦ Real.exp (X i w))
      (fun _ _ ↦ (Real.exp_pos _).le) (Finset.mem_univ j))

theorem expMax_expectation_young {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [Nonempty ι]
    (μ : Measure Ω) (X Y : ι → Ω → ℝ) (p : ℝ) (hp : 0 < p)
    (hmX : ∀ i, Measurable (X i)) (hmY : ∀ i, Measurable (Y i))
    (hX₁ : ∀ i, Integrable (fun w ↦ Real.exp (X i w)) μ)
    (hY₁ : ∀ i, Integrable (fun w ↦ Real.exp (Y i w)) μ)
    (hX₂ : ∀ i, Integrable (fun w ↦ Real.exp (2*X i w)) μ)
    (hY₂ : ∀ i, Integrable (fun w ↦ Real.exp (2*Y i w)) μ)
    (hΔ₂ : ∀ i, Integrable (fun w ↦ (X i w-Y i w)^2) μ) :
    |(∫ w, Real.exp (⨆ i, X i w) ∂μ) - (∫ w, Real.exp (⨆ i, Y i w) ∂μ)| ≤
    (p/2)* (∑ i, ∫ w, (X i w-Y i w)^2 ∂μ) +
      ((∑ i, ∫ w, Real.exp (2*X i w) ∂μ)+(∑ i, ∫ w, Real.exp (2*Y i w) ∂μ))/p := by
  classical
  let F w := Real.exp (⨆ i, X i w)
  let G w := Real.exp (⨆ i, Y i w)
  let δ i w := (X i w-Y i w)^2
  let E i w := Real.exp (2*X i w)+Real.exp (2*Y i w)
  let R i w := (p/2)*δ i w+E i w/p
  have hIF : Integrable F μ := integrable_exp_fin_sup μ X hmX hX₁
  have hIG : Integrable G μ := integrable_exp_fin_sup μ Y hmY hY₁
  have hIE i : Integrable (E i) μ := (hX₂ i).add (hY₂ i)
  have hIR i : Integrable (R i) μ := ((hΔ₂ i).const_mul _).add ((hIE i).div_const p)
  have hIRsum : Integrable (fun w ↦ ∑ i, R i w) μ := integrable_finsetSum _ (fun i _ ↦ hIR i)
  have hP (w : Ω) : |F w-G w| ≤ ∑ i, R i w :=
    (finite_expMax_abs_sub_le_sum (fun i ↦ X i w) (fun i ↦ Y i w)).trans
      (Finset.sum_le_sum (fun i _ ↦ exp_abs_sub_young (X i w) (Y i w) p hp))
  change |(∫ w, F w ∂μ) - (∫ w, G w ∂μ)| ≤ _
  rw [← integral_sub hIF hIG]
  calc
    _ ≤ ∫ w, |F w-G w| ∂μ := by
      simpa only [Real.norm_eq_abs] using (norm_integral_le_integral_norm (fun w ↦ F w-G w))
    _ ≤ ∫ w, ∑ i, R i w ∂μ :=
      integral_mono_of_nonneg (Eventually.of_forall (fun _ ↦ abs_nonneg _)) hIRsum (Eventually.of_forall hP)
    _ = _ := by
      rw [integral_finsetSum _ (fun i _ ↦ hIR i)]
      have he (i : ι) : (∫ w, R i w ∂μ) =
          (p/2)*(∫ w, δ i w ∂μ) +
          ((∫ w, Real.exp (2*X i w) ∂μ)+(∫ w, Real.exp (2*Y i w) ∂μ))/p := by
        unfold R δ E
        rw [integral_add ((hΔ₂ i).const_mul _) ((hIE i).div_const p),
          integral_const_mul,integral_div,integral_add (hX₂ i) (hY₂ i)]
      simp_rw [he, div_eq_mul_inv, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
      rw [Finset.sum_add_distrib]
end CubeBrownian
#print axioms CubeBrownian.expMax_expectation_young
