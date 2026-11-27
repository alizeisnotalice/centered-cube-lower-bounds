import TrueTiltBaselineLimits

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


/-- The actual centered anchor/relative covariance differs from the true raw
anchor/relative product by an additive o(1), even if the anchor variance
itself diverges. A raw cross bound therefore transfers without enlargement
apart from a vanishing error. -/
theorem true_winner_base_inc_cov_difference_tendsto
    (X Y : ℕ → Ω → ℝ) (a : ℕ → ℝ)
    (hX : ∀ n, Measurable (X n)) (hY : ∀ n, Measurable (Y n))
    (ha0 : ∀ n, 0 ≤ a n) (ha : ∀ n, a n ≤ 1/2)
    (hx : ∀ n w, |X n w| ≤ a n) (hy : ∀ n w, |Y n w| ≤ a n)
    (hEX : ∀ n, (∫ w, X n w ∂P)=0)
    (hsmall : Tendsto (fun n : ℕ ↦ (n:ℝ)*a n*
      (rawSq P (X n)+rawSq P (fun w ↦ Y n w-X n w))) atTop (𝓝 0))
    (hbase : Tendsto (fun n ↦ winnerBaseMean P (X n)) atTop (𝓝 0))
    {m : ℝ}
    (hinc : Tendsto (fun n : ℕ ↦ (n:ℝ)*tiltedIncMean P (X n) (Y n)) atTop (𝓝 m)) :
    Tendsto (fun n : ℕ ↦ (n:ℝ)*
      (covariance (winnerBaseLog (X n)) (logInc (X n) (Y n)) (winnerTilt P (X n)) -
        ∫ w, X n w*(Y n w-X n w) ∂P)) atTop (𝓝 0) := by
  have hlim : Tendsto (fun n : ℕ ↦ 5*((n:ℝ)*a n*
    (rawSq P (X n)+rawSq P (fun w ↦ Y n w-X n w))) +
    |winnerBaseMean P (X n)| * |(n:ℝ)*tiltedIncMean P (X n) (Y n)|)
    atTop (𝓝 0) := by
    simpa using (hsmall.const_mul 5).add (hbase.abs.mul hinc.abs)
  refine zero_limit_of_abs_bound hlim (Eventually.of_forall fun n ↦ ?_)
  rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg n : (0:ℝ) ≤ n)]
  calc
    _ ≤ (n:ℝ)*(5*a n*(rawSq P (X n)+rawSq P (fun w ↦ Y n w-X n w)) +
        |winnerBaseMean P (X n)| * |tiltedIncMean P (X n) (Y n)|) :=
      mul_le_mul_of_nonneg_left (true_winner_base_inc_cov_error P (X n) (Y n)
        (hX n) (hY n) (ha0 n) (ha n) (hx n) (hy n) (hEX n)) (Nat.cast_nonneg n)
    _ = _ := by rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg n : (0:ℝ) ≤ n)]; ring

end
end CubeSqrtProbability
#print axioms CubeSqrtProbability.true_winner_base_inc_cov_difference_tendsto
