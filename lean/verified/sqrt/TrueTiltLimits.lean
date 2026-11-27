import TrueTiltCenteredCovariance

open MeasureTheory ProbabilityTheory Filter Topology
namespace CubeSqrtProbability

private theorem tendsto_of_error_le
    {u v e : ℕ → ℝ} {l : ℝ}
    (hv : Tendsto v atTop (𝓝 l)) (he : Tendsto e atTop (𝓝 0))
    (h : ∀ᶠ n in atTop, |u n - v n| ≤ e n) :
    Tendsto u atTop (𝓝 l) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (by simpa using hv.sub he) (by simpa using hv.add he)
  · filter_upwards [h] with n hn
    linarith [(abs_le.mp hn).1]
  · filter_upwards [h] with n hn
    linarith [(abs_le.mp hn).2]

private theorem scaled_abs_bound {a b c : ℝ} (n : ℕ) (h : |a-b| ≤ c) :
    |(n:ℝ)*a-(n:ℝ)*b| ≤ (n:ℝ)*c := by
  rw [← mul_sub, abs_mul, abs_of_nonneg (Nat.cast_nonneg n : 0 ≤ (n:ℝ))]
  exact mul_le_mul_of_nonneg_left h (Nat.cast_nonneg n)

section
variable {Ω : Type*} [MeasurableSpace Ω]
variable (P : Measure Ω) [IsProbabilityMeasure P]

noncomputable def winnerTilt (X : Ω → ℝ) : Measure Ω :=
  P.tilted (fun w ↦ Real.log (1+X w))

noncomputable def rawSq (X : Ω → ℝ) : ℝ := ∫ w, X w^2 ∂P

noncomputable def rawIncCross (X Y Z : Ω → ℝ) : ℝ :=
  ∫ w, (Y w-X w)*(Z w-X w) ∂P

noncomputable def tiltedIncMean (X Y : Ω → ℝ) : ℝ :=
  ∫ w, logInc X Y w ∂(winnerTilt P X)

/-- Mean of the sum of true log increments, tilted at the actual winner
node, from the raw untilted second moment and small-load estimate. -/
theorem true_winner_tilted_mean_tendsto (X Y : ℕ → Ω → ℝ) (a : ℕ → ℝ)
    (hX : ∀ n, Measurable (X n)) (hY : ∀ n, Measurable (Y n))
    (ha : ∀ n, a n ≤ 1/2)
    (hx : ∀ n w, |X n w| ≤ a n) (hy : ∀ n w, |Y n w| ≤ a n)
    (hEX : ∀ n, (∫ w, X n w ∂P) = 0)
    (hEY : ∀ n, (∫ w, Y n w ∂P) = 0)
    {D : ℝ}
    (hD : Tendsto (fun n : ℕ ↦ (n:ℝ) * rawSq P (fun w ↦ Y n w-X n w)) atTop (𝓝 D))
    (hsmall : Tendsto (fun n : ℕ ↦ (n:ℝ) * a n * (rawSq P (X n)+rawSq P (Y n)))
      atTop (𝓝 0)) :
    Tendsto (fun n : ℕ ↦ (n:ℝ) * tiltedIncMean P (X n) (Y n)) atTop (𝓝 (-D/2)) := by
  have hv : Tendsto (fun n : ℕ ↦ -((n:ℝ)*rawSq P (fun w ↦ Y n w-X n w))/2)
      atTop (𝓝 (-D/2)) := hD.neg.div_const _
  have he : Tendsto (fun n : ℕ ↦ 4*((n:ℝ)*a n*(rawSq P (X n)+rawSq P (Y n))))
      atTop (𝓝 0) := by simpa using hsmall.const_mul 4
  refine tendsto_of_error_le hv he (Eventually.of_forall fun n : ℕ ↦ ?_)
  have h := single_tilt_log_difference_mean P (X n) (Y n) (hX n) (hY n)
    (ha n) (hx n) (hy n) (hEX n) (hEY n)
  have hs : |(n:ℝ)*tiltedIncMean P (X n) (Y n) -
      (n:ℝ)*(-(rawSq P (fun w ↦ Y n w-X n w))/2)| ≤
      (n:ℝ)*(4*a n*(rawSq P (X n)+rawSq P (Y n))) := by
    apply scaled_abs_bound
    simpa only [tiltedIncMean, winnerTilt, rawSq, sub_neg_eq_add, neg_div] using h
  have e1 : (n:ℝ)*(-(rawSq P (fun w ↦ Y n w-X n w))/2) =
      -((n:ℝ)*rawSq P (fun w ↦ Y n w-X n w))/2 := by ring
  have e2 : (n:ℝ)*(4*a n*(rawSq P (X n)+rawSq P (Y n))) =
      4*((n:ℝ)*a n*(rawSq P (X n)+rawSq P (Y n))) := by ring
  rw [e1,e2] at hs
  exact hs

/-- Covariance of the sums of true log increments, under the common true
winner tilt. Only the raw untilted crosses have to be supplied by the source. -/
theorem true_winner_tilted_covariance_tendsto
    (X Y Z : ℕ → Ω → ℝ) (a : ℕ → ℝ)
    (hX : ∀ n, Measurable (X n)) (hY : ∀ n, Measurable (Y n))
    (hZ : ∀ n, Measurable (Z n))
    (ha0 : ∀ n, 0 ≤ a n) (ha : ∀ n, a n ≤ 1/2)
    (hx : ∀ n w, |X n w| ≤ a n) (hy : ∀ n w, |Y n w| ≤ a n)
    (hz : ∀ n w, |Z n w| ≤ a n) (hEX : ∀ n, (∫ w, X n w ∂P) = 0)
    (haLim : Tendsto a atTop (𝓝 0))
    {DY DZ CY CZ C : ℝ}
    (hDY : Tendsto (fun n : ℕ ↦ (n:ℝ)*rawSq P (fun w ↦ Y n w-X n w)) atTop (𝓝 DY))
    (hDZ : Tendsto (fun n : ℕ ↦ (n:ℝ)*rawSq P (fun w ↦ Z n w-X n w)) atTop (𝓝 DZ))
    (hMY : Tendsto (fun n : ℕ ↦ (n:ℝ)*tiltedIncMean P (X n) (Y n)) atTop (𝓝 CY))
    (hMZ : Tendsto (fun n : ℕ ↦ (n:ℝ)*tiltedIncMean P (X n) (Z n)) atTop (𝓝 CZ))
    (hC : Tendsto (fun n : ℕ ↦ (n:ℝ)*rawIncCross P (X n) (Y n) (Z n)) atTop (𝓝 C)) :
    Tendsto (fun n : ℕ ↦ (n:ℝ)*covariance (logInc (X n) (Y n)) (logInc (X n) (Z n))
      (winnerTilt P (X n))) atTop (𝓝 C) := by
  have hYabs := hMY.abs
  have hZabs := hMZ.abs
  have hinv : Tendsto (fun n : ℕ ↦ ((n:ℝ)⁻¹)) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hcent : Tendsto (fun n : ℕ ↦ |(n:ℝ)*tiltedIncMean P (X n) (Y n)| *
      |(n:ℝ)*tiltedIncMean P (X n) (Z n)| * ((n:ℝ)⁻¹)) atTop (𝓝 0) := by
    simpa using (hYabs.mul hZabs).mul hinv
  have hraw : Tendsto (fun n : ℕ ↦ 5*a n*((n:ℝ)*rawSq P (fun w ↦ Y n w-X n w) +
      (n:ℝ)*rawSq P (fun w ↦ Z n w-X n w))) atTop (𝓝 0) := by
    simpa using (haLim.const_mul 5).mul (hDY.add hDZ)
  have he := hraw.add hcent
  refine tendsto_of_error_le hC (by simpa using he) ?_
  filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
  have hn0 : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have hc := true_single_tilt_centered_increment_covariance P (X n) (X n) (Y n) (X n) (Z n)
    (hX n) (hX n) (hY n) (hX n) (hZ n) (ha0 n) (ha n) (hx n) (hx n) (hy n)
    (hx n) (hz n) (hEX n)
  have hs := scaled_abs_bound n hc
  refine hs.trans_eq ?_
  simp only [rawSq, tiltedIncMean, winnerTilt]
  field_simp

end
end CubeSqrtProbability
#print axioms CubeSqrtProbability.true_winner_tilted_mean_tendsto
#print axioms CubeSqrtProbability.true_winner_tilted_covariance_tendsto
