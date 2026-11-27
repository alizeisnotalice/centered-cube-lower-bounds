import TrueTiltLimits

open MeasureTheory ProbabilityTheory Filter Topology
namespace CubeSqrtProbability

section
variable {Ω : Type*} [MeasurableSpace Ω]
variable (P : Measure Ω) [IsProbabilityMeasure P]

noncomputable def winnerBaseLog (X : Ω → ℝ) (w : Ω) : ℝ := Real.log (1+X w)
noncomputable def winnerBaseMean (X : Ω → ℝ) : ℝ :=
  ∫ w, winnerBaseLog X w ∂(winnerTilt P X)

theorem true_winner_base_mean_error (X : Ω → ℝ)
    (hX : Measurable X) {a : ℝ} (ha : a ≤ 1/2) (hx : ∀ w, |X w| ≤ a)
    (hEX : (∫ w, X w ∂P)=0) :
    |winnerBaseMean P X - rawSq P X / 2| ≤ 4*a*rawSq P X := by
  have H := single_tilt_log_mean_integrated P X X hX hX ha hx hx hEX hEX
  simp only [← pow_two] at H
  rw [show (∫ w, X w^2 ∂P) - (∫ w, X w^2 ∂P)/2 = (∫ w, X w^2 ∂P)/2 by ring] at H
  exact H

theorem true_winner_base_mean_abs_le (X : Ω → ℝ)
    (hX : Measurable X) {a : ℝ} (ha : a ≤ 1/2) (hx : ∀ w, |X w| ≤ a)
    (hEX : (∫ w, X w ∂P)=0) :
    |winnerBaseMean P X| ≤ (5/2)*rawSq P X := by
  have hq : 0 ≤ rawSq P X := integral_nonneg fun w ↦ sq_nonneg (X w)
  have err := true_winner_base_mean_error P X hX ha hx hEX
  rw [show winnerBaseMean P X = (winnerBaseMean P X - rawSq P X / 2) + rawSq P X / 2 by ring]
  refine (abs_add_le _ _).trans ?_
  rw [abs_of_nonneg (by positivity : 0 ≤ rawSq P X / 2)]
  have hb := mul_le_mul_of_nonneg_right ha hq
  linarith

theorem true_winner_base_inc_cov_error (X Y : Ω → ℝ)
    (hX : Measurable X) (hY : Measurable Y)
    {a : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ 1/2)
    (hx : ∀ w, |X w| ≤ a) (hy : ∀ w, |Y w| ≤ a)
    (hEX : (∫ w, X w ∂P)=0) :
    |covariance (winnerBaseLog X) (logInc X Y) (winnerTilt P X) -
      ∫ w, X w*(Y w-X w) ∂P| ≤
      5*a*(rawSq P X+rawSq P (fun w ↦ Y w-X w)) +
      |winnerBaseMean P X| * |tiltedIncMean P X Y| := by
  have H := true_single_tilt_centered_increment_covariance P X (fun _ ↦ (0:ℝ)) X X Y hX
    measurable_const hX hX hY ha0 ha hx
    (fun _ ↦ by simpa using ha0) hx hx hy hEX
  have h0 : logInc (fun _ : Ω ↦ (0:ℝ)) X = winnerBaseLog X := by
    funext w
    simp [logInc, winnerBaseLog]
  rw [h0] at H
  simpa only [sub_zero, winnerTilt, tiltedIncMean, winnerBaseMean, rawSq] using H

theorem true_winner_base_variance_error (X : Ω → ℝ)
    (hX : Measurable X) {a : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ 1/2)
    (hx : ∀ w, |X w| ≤ a) (hEX : (∫ w, X w ∂P)=0) :
    |covariance (winnerBaseLog X) (winnerBaseLog X) (winnerTilt P X) - rawSq P X|
      ≤ 10*a*rawSq P X + |winnerBaseMean P X|^2 := by
  have H := true_single_tilt_centered_increment_covariance P X (fun _ ↦ (0:ℝ)) X
    (fun _ ↦ (0:ℝ)) X hX measurable_const hX measurable_const hX ha0 ha hx
    (fun _ ↦ by simpa using ha0) hx (fun _ ↦ by simpa using ha0) hx hEX
  have h0 : logInc (fun _ : Ω ↦ (0:ℝ)) X = winnerBaseLog X := by
    funext w
    simp [logInc, winnerBaseLog]
  rw [h0] at H
  simp only [sub_zero, ← pow_two] at H
  change |covariance (winnerBaseLog X) (winnerBaseLog X) (winnerTilt P X)-rawSq P X| ≤
    5*a*(rawSq P X+rawSq P X)+|winnerBaseMean P X|^2 at H
  have e : 5*a*(rawSq P X+rawSq P X) = 10*a*rawSq P X := by ring
  rwa [e] at H

end
end CubeSqrtProbability
#print axioms CubeSqrtProbability.true_winner_base_mean_error
#print axioms CubeSqrtProbability.true_winner_base_mean_abs_le
#print axioms CubeSqrtProbability.true_winner_base_inc_cov_error
#print axioms CubeSqrtProbability.true_winner_base_variance_error
