import TrueTiltBaseline

open MeasureTheory ProbabilityTheory Filter Topology
namespace CubeSqrtProbability

private theorem zero_limit_of_abs_bound {f g : ℕ → ℝ}
    (hg : Tendsto g atTop (𝓝 0)) (h : ∀ᶠ n in atTop, |f n| ≤ g n) :
    Tendsto f atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (by simpa using hg.neg) hg
  · exact h.mono fun n hn ↦ (abs_le.mp hn).1
  · exact h.mono fun n hn ↦ (abs_le.mp hn).2

section
variable {Ω : Type*} [MeasurableSpace Ω]
variable (P : Measure Ω) [IsProbabilityMeasure P]

/-- The difference between the scaled anchor log mean and half the scaled
raw anchor variance vanishes, without requiring that variance to converge. -/
theorem true_winner_base_mean_difference_tendsto
    (X : ℕ → Ω → ℝ) (a : ℕ → ℝ) (hX : ∀ n, Measurable (X n))
    (ha : ∀ n, a n ≤ 1/2) (hx : ∀ n w, |X n w| ≤ a n)
    (hEX : ∀ n, (∫ w, X n w ∂P)=0)
    (hsmall : Tendsto (fun n : ℕ ↦ (n:ℝ)*a n*rawSq P (X n)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ ↦ (n:ℝ)*winnerBaseMean P (X n) - (n:ℝ)*rawSq P (X n)/2)
      atTop (𝓝 0) := by
  refine zero_limit_of_abs_bound (g := fun n : ℕ ↦ 4*((n:ℝ)*a n*rawSq P (X n)))
    (by simpa using hsmall.const_mul 4) (Eventually.of_forall fun n ↦ ?_)
  rw [show (n:ℝ)*winnerBaseMean P (X n) - (n:ℝ)*rawSq P (X n)/2 =
    (n:ℝ)*(winnerBaseMean P (X n)-rawSq P (X n)/2) by ring,
    abs_mul,abs_of_nonneg (Nat.cast_nonneg n : 0 ≤ (n:ℝ))]
  calc
    _ ≤ (n:ℝ)*(4*a n*rawSq P (X n)) := mul_le_mul_of_nonneg_left
      (true_winner_base_mean_error P (X n) (hX n) (ha n) (hx n) (hEX n)) (Nat.cast_nonneg _)
    _ = _ := by ring

/-- The centered anchor variance is asymptotic to the actual scaled
untilted variance up to a vanishing *additive* error. -/
theorem true_winner_base_variance_difference_tendsto
    (X : ℕ → Ω → ℝ) (a : ℕ → ℝ) (hX : ∀ n, Measurable (X n))
    (ha0 : ∀ n, 0 ≤ a n) (ha : ∀ n, a n ≤ 1/2) (hx : ∀ n w, |X n w| ≤ a n)
    (hEX : ∀ n, (∫ w, X n w ∂P)=0)
    (hsmall : Tendsto (fun n : ℕ ↦ (n:ℝ)*a n*rawSq P (X n)) atTop (𝓝 0))
    (hsmall2 : Tendsto (fun n : ℕ ↦ ((n:ℝ)*rawSq P (X n))^2 / (n:ℝ))
      atTop (𝓝 0)) :
    Tendsto (fun n : ℕ ↦ (n:ℝ)*covariance (winnerBaseLog (X n)) (winnerBaseLog (X n))
      (winnerTilt P (X n)) - (n:ℝ)*rawSq P (X n)) atTop (𝓝 0) := by
  have lim : Tendsto (fun n : ℕ ↦ 10*((n:ℝ)*a n*rawSq P (X n)) +
      (5/2)^2*(((n:ℝ)*rawSq P (X n))^2 / (n:ℝ))) atTop (𝓝 0) := by
    simpa using (hsmall.const_mul 10).add (hsmall2.const_mul ((5/2)^2))
  refine zero_limit_of_abs_bound lim ?_
  filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
  have hn0 : (0:ℝ) < n := Nat.cast_pos.mpr hn
  let b := winnerBaseMean P (X n)
  let q := rawSq P (X n)
  have hmean : |b| ≤ (5/2)*q :=
    true_winner_base_mean_abs_le P (X n) (hX n) (ha n) (hx n) (hEX n)
  have hcenter := pow_le_pow_left₀ (abs_nonneg _) hmean 2
  rw [← mul_sub, abs_mul, abs_of_pos hn0]
  calc
    _ ≤ (n:ℝ)*(10*a n*q+|b|^2) := mul_le_mul_of_nonneg_left
      (true_winner_base_variance_error P (X n) (hX n) (ha0 n) (ha n) (hx n) (hEX n)) hn0.le
    _ ≤ (n:ℝ)*(10*a n*q+((5/2)*q)^2) :=
      mul_le_mul_of_nonneg_left (add_le_add (le_refl _) hcenter) hn0.le
    _ = _ := by change (n:ℝ)*(10*a n*q+((5/2)*q)^2) =
                   10*((n:ℝ)*a n*q)+(5/2)^2*(((n:ℝ)*q)^2/(n:ℝ))
                field_simp

end
end CubeSqrtProbability
#print axioms CubeSqrtProbability.true_winner_base_mean_difference_tendsto
#print axioms CubeSqrtProbability.true_winner_base_variance_difference_tendsto
