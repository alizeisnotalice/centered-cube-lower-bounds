import ProbabilityApproximation.ChenShao.UniformBerryEsseen

open MeasureTheory ProbabilityTheory Set
namespace CubeMD

theorem finite_row_berry_closed_cdf {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    [DecidableEq ι] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} (hm : ∀ i, Measurable (X i))
    (h2 : ∀ i, MemLp (X i) 2 μ) (hind : iIndepFun X μ)
    (hzero : ∀ i, ∫ w, X i w ∂μ = 0) (hv : ∑ i, variance (X i) μ = 1)
    (h3 : ∀ i, Integrable (fun w ↦ |X i w| ^ 3) μ)
    (δ : ℝ) (hδ : 30 * (∑ i, ∫ w, |X i w| ^ 3 ∂μ) ≤ δ) :
    ∀ x : ℝ, |(μ.map (fun w ↦ ∑ i, X i w)).real (Iic x)
      - (gaussianReal 0 1).real (Iic x)| ≤ δ := by
  intro x
  have hh := uniformBerryEsseen_thirdMoment h2 hm hind hzero hv h3 x
  rw [cdf_eq_real (μ := μ.map (fun w ↦ ∑ i, X i w)),
      cdf_eq_real (μ := gaussianReal 0 1)] at hh
  exact hh.trans hδ

theorem fin_row_berry_closed_cdf {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {n : ℕ} {X : Fin n → Ω → ℝ}
    (hm : ∀ i, Measurable (X i)) (h2 : ∀ i, MemLp (X i) 2 μ)
    (hind : iIndepFun X μ) (hzero : ∀ i, ∫ w, X i w ∂μ = 0)
    (hv : ∑ i, variance (X i) μ = 1)
    (h3 : ∀ i, Integrable (fun w ↦ |X i w| ^ 3) μ)
    (B : ℝ) (hB : ∀ i, (∫ w, |X i w| ^ 3 ∂μ) ≤ B) :
    ∀ x : ℝ, |(μ.map (fun w ↦ ∑ i, X i w)).real (Iic x)
      - (gaussianReal 0 1).real (Iic x)| ≤ 30 * (n * B) := by
  apply finite_row_berry_closed_cdf hm h2 hind hzero hv h3
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  calc
    _ ≤ ∑ _i : Fin n, B := Finset.sum_le_sum fun i _ ↦ hB i
    _ = _ := by simp

end CubeMD
#print axioms CubeMD.finite_row_berry_closed_cdf
#print axioms CubeMD.fin_row_berry_closed_cdf
