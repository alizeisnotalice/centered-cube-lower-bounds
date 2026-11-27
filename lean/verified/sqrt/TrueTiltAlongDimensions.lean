import TrueTiltCrossLimits
import TrueTiltPolarization

open MeasureTheory ProbabilityTheory Filter Topology
namespace CubeSqrtProbability
set_option maxHeartbeats 1100000

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

private theorem zero_limit_of_abs_bound {f g : ℕ → ℝ}
    (hg : Tendsto g atTop (𝓝 0)) (h : ∀ᶠ n in atTop, |f n| ≤ g n) :
    Tendsto f atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (by simpa using hg.neg) hg
  · exact h.mono fun n hn ↦ (abs_le.mp hn).1
  · exact h.mono fun n hn ↦ (abs_le.mp hn).2

section
variable {Ω : Type*} [MeasurableSpace Ω]
variable (P : Measure Ω) [IsProbabilityMeasure P]

/-- Mean of the sum of true log increments, tilted at the actual winner
node, from the raw untilted second moment and small-load estimate. -/
theorem true_winner_tilted_mean_tendsto_along_dimensions (m : ℕ→ℕ) (X Y : ℕ → Ω → ℝ) (a : ℕ → ℝ)
    (hX : ∀ n, Measurable (X n)) (hY : ∀ n, Measurable (Y n))
    (ha : ∀ n, a n ≤ 1/2)
    (hx : ∀ n w, |X n w| ≤ a n) (hy : ∀ n w, |Y n w| ≤ a n)
    (hEX : ∀ n, (∫ w, X n w ∂P) = 0)
    (hEY : ∀ n, (∫ w, Y n w ∂P) = 0)
    {D : ℝ}
    (hD : Tendsto (fun n : ℕ ↦ (m n:ℝ) * rawSq P (fun w ↦ Y n w-X n w)) atTop (𝓝 D))
    (hsmall : Tendsto (fun n : ℕ ↦ (m n:ℝ) * a n * (rawSq P (X n)+rawSq P (Y n)))
      atTop (𝓝 0)) :
    Tendsto (fun n : ℕ ↦ (m n:ℝ) * tiltedIncMean P (X n) (Y n)) atTop (𝓝 (-D/2)) := by
  have hv : Tendsto (fun n : ℕ ↦ -((m n:ℝ)*rawSq P (fun w ↦ Y n w-X n w))/2)
      atTop (𝓝 (-D/2)) := hD.neg.div_const _
  have he : Tendsto (fun n : ℕ ↦ 4*((m n:ℝ)*a n*(rawSq P (X n)+rawSq P (Y n))))
      atTop (𝓝 0) := by simpa using hsmall.const_mul 4
  refine tendsto_of_error_le hv he (Eventually.of_forall fun n : ℕ ↦ ?_)
  have h := single_tilt_log_difference_mean P (X n) (Y n) (hX n) (hY n)
    (ha n) (hx n) (hy n) (hEX n) (hEY n)
  have hs : |(m n:ℝ)*tiltedIncMean P (X n) (Y n) -
      (m n:ℝ)*(-(rawSq P (fun w ↦ Y n w-X n w))/2)| ≤
      (m n:ℝ)*(4*a n*(rawSq P (X n)+rawSq P (Y n))) := by
    apply scaled_abs_bound
    simpa only [tiltedIncMean, winnerTilt, rawSq, sub_neg_eq_add, neg_div] using h
  have e1 : (m n:ℝ)*(-(rawSq P (fun w ↦ Y n w-X n w))/2) =
      -((m n:ℝ)*rawSq P (fun w ↦ Y n w-X n w))/2 := by ring
  have e2 : (m n:ℝ)*(4*a n*(rawSq P (X n)+rawSq P (Y n))) =
      4*((m n:ℝ)*a n*(rawSq P (X n)+rawSq P (Y n))) := by ring
  rw [e1,e2] at hs
  exact hs

/-- Covariance of the sums of true log increments, under the common true
winner tilt. Only the raw untilted crosses have to be supplied by the source. -/
theorem true_winner_tilted_covariance_tendsto_along_dimensions (m : ℕ→ℕ) (hm : Tendsto m atTop atTop)
    (X Y Z : ℕ → Ω → ℝ) (a : ℕ → ℝ)
    (hX : ∀ n, Measurable (X n)) (hY : ∀ n, Measurable (Y n))
    (hZ : ∀ n, Measurable (Z n))
    (ha0 : ∀ n, 0 ≤ a n) (ha : ∀ n, a n ≤ 1/2)
    (hx : ∀ n w, |X n w| ≤ a n) (hy : ∀ n w, |Y n w| ≤ a n)
    (hz : ∀ n w, |Z n w| ≤ a n) (hEX : ∀ n, (∫ w, X n w ∂P) = 0)
    (haLim : Tendsto a atTop (𝓝 0))
    {DY DZ CY CZ C : ℝ}
    (hDY : Tendsto (fun n : ℕ ↦ (m n:ℝ)*rawSq P (fun w ↦ Y n w-X n w)) atTop (𝓝 DY))
    (hDZ : Tendsto (fun n : ℕ ↦ (m n:ℝ)*rawSq P (fun w ↦ Z n w-X n w)) atTop (𝓝 DZ))
    (hMY : Tendsto (fun n : ℕ ↦ (m n:ℝ)*tiltedIncMean P (X n) (Y n)) atTop (𝓝 CY))
    (hMZ : Tendsto (fun n : ℕ ↦ (m n:ℝ)*tiltedIncMean P (X n) (Z n)) atTop (𝓝 CZ))
    (hC : Tendsto (fun n : ℕ ↦ (m n:ℝ)*rawIncCross P (X n) (Y n) (Z n)) atTop (𝓝 C)) :
    Tendsto (fun n : ℕ ↦ (m n:ℝ)*covariance (logInc (X n) (Y n)) (logInc (X n) (Z n))
      (winnerTilt P (X n))) atTop (𝓝 C) := by
  have hYabs := hMY.abs
  have hZabs := hMZ.abs
  have hinv : Tendsto (fun n : ℕ ↦ ((m n:ℝ)⁻¹)) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp hm)
  have hcent : Tendsto (fun n : ℕ ↦ |(m n:ℝ)*tiltedIncMean P (X n) (Y n)| *
      |(m n:ℝ)*tiltedIncMean P (X n) (Z n)| * ((m n:ℝ)⁻¹)) atTop (𝓝 0) := by
    simpa using (hYabs.mul hZabs).mul hinv
  have hraw : Tendsto (fun n : ℕ ↦ 5*a n*((m n:ℝ)*rawSq P (fun w ↦ Y n w-X n w) +
      (m n:ℝ)*rawSq P (fun w ↦ Z n w-X n w))) atTop (𝓝 0) := by
    simpa using (haLim.const_mul 5).mul (hDY.add hDZ)
  have he := hraw.add hcent
  refine tendsto_of_error_le hC (by simpa using he) ?_
  filter_upwards [hm.eventually_gt_atTop (0:ℕ)] with n hn
  have hn0 : (0:ℝ) < m n := Nat.cast_pos.mpr hn
  have hc := true_single_tilt_centered_increment_covariance P (X n) (X n) (Y n) (X n) (Z n)
    (hX n) (hX n) (hY n) (hX n) (hZ n) (ha0 n) (ha n) (hx n) (hx n) (hy n)
    (hx n) (hz n) (hEX n)
  have hs := scaled_abs_bound (m n) hc
  refine hs.trans_eq ?_
  simp only [rawSq, tiltedIncMean, winnerTilt]
  field_simp

/-- Entrywise covariance convergence from the three source squared distances,
under the actual common winner-node Esscher change of measure. -/
theorem true_winner_tilted_covariance_of_distances_along_dimensions (m : ℕ→ℕ) (hm : Tendsto m atTop atTop)
    (X Y Z : ℕ → Ω → ℝ) (a : ℕ → ℝ)
    (hX : ∀ n, Measurable (X n)) (hY : ∀ n, Measurable (Y n)) (hZ : ∀ n, Measurable (Z n))
    (ha0 : ∀ n, 0 ≤ a n) (ha : ∀ n, a n ≤ 1/2)
    (hx : ∀ n w, |X n w| ≤ a n) (hy : ∀ n w, |Y n w| ≤ a n)
    (hz : ∀ n w, |Z n w| ≤ a n)
    (hEX : ∀ n, (∫ w, X n w ∂P) = 0)
    (hEY : ∀ n, (∫ w, Y n w ∂P) = 0)
    (hEZ : ∀ n, (∫ w, Z n w ∂P) = 0)
    (haLim : Tendsto a atTop (𝓝 0))
    {DY DZ DYZ : ℝ}
    (hDY : Tendsto (fun n : ℕ ↦ (m n:ℝ)*rawSq P (fun w ↦ Y n w-X n w)) atTop (𝓝 DY))
    (hDZ : Tendsto (fun n : ℕ ↦ (m n:ℝ)*rawSq P (fun w ↦ Z n w-X n w)) atTop (𝓝 DZ))
    (hDYZ : Tendsto (fun n : ℕ ↦ (m n:ℝ)*rawSq P (fun w ↦ Y n w-Z n w)) atTop (𝓝 DYZ))
    (hsmallY : Tendsto (fun n : ℕ ↦ (m n:ℝ)*a n*(rawSq P (X n)+rawSq P (Y n))) atTop (𝓝 0))
    (hsmallZ : Tendsto (fun n : ℕ ↦ (m n:ℝ)*a n*(rawSq P (X n)+rawSq P (Z n))) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ ↦ (m n:ℝ)*covariance (logInc (X n) (Y n)) (logInc (X n) (Z n))
      (winnerTilt P (X n))) atTop (𝓝 ((DY+DZ-DYZ)/2)) := by
  apply true_winner_tilted_covariance_tendsto_along_dimensions P m hm X Y Z a hX hY hZ ha0 ha hx hy hz hEX haLim hDY hDZ
    (true_winner_tilted_mean_tendsto_along_dimensions P m X Y a hX hY ha hx hy hEX hEY hDY hsmallY)
    (true_winner_tilted_mean_tendsto_along_dimensions P m X Z a hX hZ ha hx hz hEX hEZ hDZ hsmallZ)
  refine ((hDY.add hDZ).sub hDYZ |>.div_const (2:ℝ)).congr ?_
  intro n
  rw [raw_inc_cross_polarization P (X n) (Y n) (Z n) (hX n) (hY n) (hZ n) (hx n) (hy n) (hz n)]
  ring
/-- The difference between the scaled anchor log mean and half the scaled
raw anchor variance vanishes, without requiring that variance to converge. -/
theorem true_winner_base_mean_difference_tendsto_along_dimensions (m : ℕ→ℕ)
    (X : ℕ → Ω → ℝ) (a : ℕ → ℝ) (hX : ∀ n, Measurable (X n))
    (ha : ∀ n, a n ≤ 1/2) (hx : ∀ n w, |X n w| ≤ a n)
    (hEX : ∀ n, (∫ w, X n w ∂P)=0)
    (hsmall : Tendsto (fun n : ℕ ↦ (m n:ℝ)*a n*rawSq P (X n)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ ↦ (m n:ℝ)*winnerBaseMean P (X n) - (m n:ℝ)*rawSq P (X n)/2)
      atTop (𝓝 0) := by
  refine zero_limit_of_abs_bound (g := fun n : ℕ ↦ 4*((m n:ℝ)*a n*rawSq P (X n)))
    (by simpa using hsmall.const_mul 4) (Eventually.of_forall fun n ↦ ?_)
  rw [show (m n:ℝ)*winnerBaseMean P (X n) - (m n:ℝ)*rawSq P (X n)/2 =
    (m n:ℝ)*(winnerBaseMean P (X n)-rawSq P (X n)/2) by ring,
    abs_mul,abs_of_nonneg (Nat.cast_nonneg (m n) : 0 ≤ (m n:ℝ))]
  calc
    _ ≤ (m n:ℝ)*(4*a n*rawSq P (X n)) := mul_le_mul_of_nonneg_left
      (true_winner_base_mean_error P (X n) (hX n) (ha n) (hx n) (hEX n)) (Nat.cast_nonneg _)
    _ = _ := by ring

/-- The centered anchor variance is asymptotic to the actual scaled
untilted variance up to a vanishing *additive* error. -/
theorem true_winner_base_variance_difference_tendsto_along_dimensions (m : ℕ→ℕ) (hm : Tendsto m atTop atTop)
    (X : ℕ → Ω → ℝ) (a : ℕ → ℝ) (hX : ∀ n, Measurable (X n))
    (ha0 : ∀ n, 0 ≤ a n) (ha : ∀ n, a n ≤ 1/2) (hx : ∀ n w, |X n w| ≤ a n)
    (hEX : ∀ n, (∫ w, X n w ∂P)=0)
    (hsmall : Tendsto (fun n : ℕ ↦ (m n:ℝ)*a n*rawSq P (X n)) atTop (𝓝 0))
    (hsmall2 : Tendsto (fun n : ℕ ↦ ((m n:ℝ)*rawSq P (X n))^2 / (m n:ℝ))
      atTop (𝓝 0)) :
    Tendsto (fun n : ℕ ↦ (m n:ℝ)*covariance (winnerBaseLog (X n)) (winnerBaseLog (X n))
      (winnerTilt P (X n)) - (m n:ℝ)*rawSq P (X n)) atTop (𝓝 0) := by
  have lim : Tendsto (fun n : ℕ ↦ 10*((m n:ℝ)*a n*rawSq P (X n)) +
      (5/2)^2*(((m n:ℝ)*rawSq P (X n))^2 / (m n:ℝ))) atTop (𝓝 0) := by
    simpa using (hsmall.const_mul 10).add (hsmall2.const_mul ((5/2)^2))
  refine zero_limit_of_abs_bound lim ?_
  filter_upwards [hm.eventually_gt_atTop (0:ℕ)] with n hn
  have hn0 : (0:ℝ) < m n := Nat.cast_pos.mpr hn
  let b := winnerBaseMean P (X n)
  let q := rawSq P (X n)
  have hmean : |b| ≤ (5/2)*q :=
    true_winner_base_mean_abs_le P (X n) (hX n) (ha n) (hx n) (hEX n)
  have hcenter := pow_le_pow_left₀ (abs_nonneg _) hmean 2
  rw [← mul_sub, abs_mul, abs_of_pos hn0]
  calc
    _ ≤ (m n:ℝ)*(10*a n*q+|b|^2) := mul_le_mul_of_nonneg_left
      (true_winner_base_variance_error P (X n) (hX n) (ha0 n) (ha n) (hx n) (hEX n)) hn0.le
    _ ≤ (m n:ℝ)*(10*a n*q+((5/2)*q)^2) :=
      mul_le_mul_of_nonneg_left (add_le_add (le_refl _) hcenter) hn0.le
    _ = _ := by change (m n:ℝ)*(10*a n*q+((5/2)*q)^2) =
                   10*((m n:ℝ)*a n*q)+(5/2)^2*(((m n:ℝ)*q)^2/(m n:ℝ))
                field_simp

/-- The actual centered anchor/relative covariance differs from the true raw
anchor/relative product by an additive o(1), even if the anchor variance
itself diverges. A raw cross bound therefore transfers without enlargement
apart from a vanishing error. -/
theorem true_winner_base_inc_cov_difference_tendsto_along_dimensions (m : ℕ→ℕ)
    (X Y : ℕ → Ω → ℝ) (a : ℕ → ℝ)
    (hX : ∀ n, Measurable (X n)) (hY : ∀ n, Measurable (Y n))
    (ha0 : ∀ n, 0 ≤ a n) (ha : ∀ n, a n ≤ 1/2)
    (hx : ∀ n w, |X n w| ≤ a n) (hy : ∀ n w, |Y n w| ≤ a n)
    (hEX : ∀ n, (∫ w, X n w ∂P)=0)
    (hsmall : Tendsto (fun n : ℕ ↦ (m n:ℝ)*a n*
      (rawSq P (X n)+rawSq P (fun w ↦ Y n w-X n w))) atTop (𝓝 0))
    (hbase : Tendsto (fun n ↦ winnerBaseMean P (X n)) atTop (𝓝 0))
    {meanLimit : ℝ}
    (hinc : Tendsto (fun n : ℕ ↦ (m n:ℝ)*tiltedIncMean P (X n) (Y n)) atTop (𝓝 meanLimit)) :
    Tendsto (fun n : ℕ ↦ (m n:ℝ)*
      (covariance (winnerBaseLog (X n)) (logInc (X n) (Y n)) (winnerTilt P (X n)) -
        ∫ w, X n w*(Y n w-X n w) ∂P)) atTop (𝓝 0) := by
  have hlim : Tendsto (fun n : ℕ ↦ 5*((m n:ℝ)*a n*
    (rawSq P (X n)+rawSq P (fun w ↦ Y n w-X n w))) +
    |winnerBaseMean P (X n)| * |(m n:ℝ)*tiltedIncMean P (X n) (Y n)|)
    atTop (𝓝 0) := by
    simpa using (hsmall.const_mul 5).add (hbase.abs.mul hinc.abs)
  refine zero_limit_of_abs_bound hlim (Eventually.of_forall fun n ↦ ?_)
  rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg (m n) : (0:ℝ) ≤ m n)]
  calc
    _ ≤ (m n:ℝ)*(5*a n*(rawSq P (X n)+rawSq P (fun w ↦ Y n w-X n w)) +
        |winnerBaseMean P (X n)| * |tiltedIncMean P (X n) (Y n)|) :=
      mul_le_mul_of_nonneg_left (true_winner_base_inc_cov_error P (X n) (Y n)
        (hX n) (hY n) (ha0 n) (ha n) (hx n) (hy n) (hEX n)) (Nat.cast_nonneg (m n))
    _ = _ := by rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg (m n) : (0:ℝ) ≤ m n)]; ring


end
end CubeSqrtProbability
#print axioms CubeSqrtProbability.true_winner_tilted_mean_tendsto_along_dimensions
#print axioms CubeSqrtProbability.true_winner_tilted_covariance_tendsto_along_dimensions
#print axioms CubeSqrtProbability.true_winner_tilted_covariance_of_distances_along_dimensions
#print axioms CubeSqrtProbability.true_winner_base_mean_difference_tendsto_along_dimensions
#print axioms CubeSqrtProbability.true_winner_base_variance_difference_tendsto_along_dimensions
#print axioms CubeSqrtProbability.true_winner_base_inc_cov_difference_tendsto_along_dimensions
