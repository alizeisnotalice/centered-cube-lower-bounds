import ActualWinnerRate

open scoped NNReal BigOperators
namespace CubeSqrtProbability

theorem winner_facet_third_bound {ι : Type*} [Fintype ι]
    (s : ι → ℝ≥0) {B D U : ℝ} (hB0 : 0≤B) (hB : B≤D*U)
    (hcoord : ∀ i, √(s i:ℝ) ≤ D*U) :
    0 ≤ (2*B)^3 + stdGaussianThird*∑ i, (√(s i:ℝ))^3 ∧
    (2*B)^3 + stdGaussianThird*∑ i, (√(s i:ℝ))^3 ≤
      ((2*D)^3+stdGaussianThird*(Fintype.card ι:ℝ)*D^3)*U^3 := by
  have hg : 0 ≤ stdGaussianThird := by
    unfold stdGaussianThird
    positivity
  constructor
  · exact add_nonneg (by positivity) (mul_nonneg hg (Finset.sum_nonneg fun i _ ↦ by positivity))
  have hs : (∑ i, (√(s i:ℝ))^3) ≤ (Fintype.card ι:ℝ)*(D*U)^3 := by
    calc
      _ ≤ ∑ _ : ι, (D*U)^3 :=
        Finset.sum_le_sum fun i _ ↦ pow_le_pow_left₀ (Real.sqrt_nonneg _) (hcoord i) _
      _ = _ := by simp
  calc
    _ ≤ (2*(D*U))^3 + stdGaussianThird*((Fintype.card ι:ℝ)*(D*U)^3) :=
      add_le_add (pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hB (by norm_num)) _)
        (mul_le_mul_of_nonneg_left hs hg)
    _ = _ := by ring

theorem winner_facet_strip_bound {ι : Type*} [Fintype ι] (s : ι → ℝ≥0)
    (n : ℕ) {c : ℝ} (hc : 0<c)
    (hs : ∀ i, c ≤ ((n • s i : ℝ≥0):ℝ)) :
    0 ≤ (∑ i, (√(2*Real.pi*((n • s i : ℝ≥0):ℝ)))⁻¹) ∧
    (∑ i, (√(2*Real.pi*((n • s i : ℝ≥0):ℝ)))⁻¹) ≤
      (Fintype.card ι:ℝ) * (√(2*Real.pi*c))⁻¹ := by
  constructor
  · exact Finset.sum_nonneg fun _ _ ↦ by positivity
  calc
    _ ≤ ∑ _ : ι, (√(2*Real.pi*c))⁻¹ := by
      apply Finset.sum_le_sum
      intro i _
      exact inv_anti₀ (by positivity) (Real.sqrt_le_sqrt
        (mul_le_mul_of_nonneg_left (hs i) (by positivity)))
    _ = _ := by simp

end CubeSqrtProbability
#print axioms CubeSqrtProbability.winner_facet_third_bound
#print axioms CubeSqrtProbability.winner_facet_strip_bound
