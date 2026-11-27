import TrueTiltLimits

open MeasureTheory ProbabilityTheory Filter Topology
namespace CubeSqrtProbability

section
variable {Ω : Type*} [MeasurableSpace Ω]
variable (P : Measure Ω) [IsProbabilityMeasure P]

theorem raw_inc_cross_polarization (X Y Z : Ω → ℝ)
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    {a : ℝ} (hx : ∀ w, |X w| ≤ a) (hy : ∀ w, |Y w| ≤ a)
    (hz : ∀ w, |Z w| ≤ a) :
    rawIncCross P X Y Z =
      (rawSq P (fun w ↦ Y w-X w)+rawSq P (fun w ↦ Z w-X w)-
        rawSq P (fun w ↦ Y w-Z w))/2 := by
  have hi (U V : Ω → ℝ) (hU : Measurable U) (hV : Measurable V)
      (hUb : ∀ w, |U w| ≤ a) (hVb : ∀ w, |V w| ≤ a) :
      Integrable (fun w ↦ (U w-V w)^2) P := by
    apply integrable_of_uniform_abs P ((hU.sub hV).pow_const 2) (B := (2*a)^2)
    intro w
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (abs_sub_of_common_bound (hVb w) (hUb w)) _
  unfold rawIncCross rawSq
  have hA := hi Y X hY hX hy hx
  have hB := hi Z X hZ hX hz hx
  have hC := hi Y Z hY hZ hy hz
  have hab : (∫ w, (Y w-X w)^2+(Z w-X w)^2 ∂P) =
      (∫ w, (Y w-X w)^2 ∂P)+(∫ w, (Z w-X w)^2 ∂P) := integral_add hA hB
  have habc : (∫ w, ((Y w-X w)^2+(Z w-X w)^2)-(Y w-Z w)^2 ∂P) =
      (∫ w, (Y w-X w)^2+(Z w-X w)^2 ∂P)-(∫ w, (Y w-Z w)^2 ∂P) :=
    integral_sub (hA.add hB) hC
  change (∫ w, (Y w-X w)*(Z w-X w) ∂P) =
     ((∫ w, (Y w-X w)^2 ∂P)+(∫ w, (Z w-X w)^2 ∂P)-(∫ w, (Y w-Z w)^2 ∂P))/2
  rw [← hab, ← habc, ← integral_div]
  congr 1
  funext w
  ring

/-- Entrywise covariance convergence from the three source squared distances,
under the actual common winner-node Esscher change of measure. -/
theorem true_winner_tilted_covariance_of_distances
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
    (hDY : Tendsto (fun n : ℕ ↦ (n:ℝ)*rawSq P (fun w ↦ Y n w-X n w)) atTop (𝓝 DY))
    (hDZ : Tendsto (fun n : ℕ ↦ (n:ℝ)*rawSq P (fun w ↦ Z n w-X n w)) atTop (𝓝 DZ))
    (hDYZ : Tendsto (fun n : ℕ ↦ (n:ℝ)*rawSq P (fun w ↦ Y n w-Z n w)) atTop (𝓝 DYZ))
    (hsmallY : Tendsto (fun n : ℕ ↦ (n:ℝ)*a n*(rawSq P (X n)+rawSq P (Y n))) atTop (𝓝 0))
    (hsmallZ : Tendsto (fun n : ℕ ↦ (n:ℝ)*a n*(rawSq P (X n)+rawSq P (Z n))) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ ↦ (n:ℝ)*covariance (logInc (X n) (Y n)) (logInc (X n) (Z n))
      (winnerTilt P (X n))) atTop (𝓝 ((DY+DZ-DYZ)/2)) := by
  apply true_winner_tilted_covariance_tendsto P X Y Z a hX hY hZ ha0 ha hx hy hz hEX haLim hDY hDZ
    (true_winner_tilted_mean_tendsto P X Y a hX hY ha hx hy hEX hEY hDY hsmallY)
    (true_winner_tilted_mean_tendsto P X Z a hX hZ ha hx hz hEX hEZ hDZ hsmallZ)
  refine ((hDY.add hDZ).sub hDYZ |>.div_const (2:ℝ)).congr ?_
  intro n
  rw [raw_inc_cross_polarization P (X n) (Y n) (Z n) (hX n) (hY n) (hZ n) (hx n) (hy n) (hz n)]
  ring
end
end CubeSqrtProbability
#print axioms CubeSqrtProbability.raw_inc_cross_polarization
#print axioms CubeSqrtProbability.true_winner_tilted_covariance_of_distances
