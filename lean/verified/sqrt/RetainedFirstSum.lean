import RetainedInverseSquare
import PaperPacketCountRates
import Mathlib.Algebra.Order.BigOperators.Group.Finset

open Finset Filter
open scoped Topology
namespace CubeSqrtOverlap

theorem reinforced_first_sum_inverse_square
    (a b α β : ℝ) (ha : 0 < a) (hb : 0 < b) (hα : 0 ≤ α)
    (δ : ℕ → ℝ) (B : ℕ → ℕ) (R : ℕ → Finset ℕ) (score : ℕ → ℕ → ℝ)
    (hδ : ∀ᶠ n in atTop, 0 ≤ δ n)
    (hR : ∀ᶠ n in atTop, R n ⊆ range (B n))
    (hEnd : Tendsto (fun n ↦ a+(B n:ℝ)*δ n) atTop (𝓝 b))
    (hD : Tendsto (fun n ↦ δ n*((range (B n) \ R n).card:ℝ)) atTop (𝓝 0))
    (hCount : Tendsto (fun n ↦ δ n*((R n).card:ℝ)) atTop (𝓝 (b-a)))
    (hScore : ∀ᶠ n in atTop, ∀ i ∈ R n, α/(a+(i:ℝ)*δ n)^2-β ≤ score n i)
    (ε : ℝ) (he : 0 < ε) :
    ∀ᶠ n in atTop, α*(1/a-1/b)-β*(b-a)-ε ≤ δ n*(∑ i ∈ R n, score n i) := by
  let η := ε/(2*(α+1))
  have hη : 0 < η := by dsimp [η]; positivity
  have hηε : α*η ≤ ε/2 := by
    have hD : 0 < 2*(α+1) := by positivity
    have hA : α*η = (α*ε)/(2*(α+1)) := by dsimp [η]; rw [mul_div_assoc]
    rw [hA]
    exact (div_le_iff₀ hD).2 (by nlinarith only [he])
  have hInv := inverse_square_retained_lower_limit a b ha hb δ B R hδ hR hEnd hD η hη
  have hCt := (hCount.const_mul β).eventually_lt_const (show β*(b-a) < β*(b-a)+ε/2 by linarith)
  filter_upwards [hInv,hδ,hCt,hScore] with n hInv hn hc hS
  have hPoint : ∀ i ∈ R n, α*(δ n/(a+(i:ℝ)*δ n)^2)-β*δ n ≤ δ n*score n i := by
    intro i hi
    have h := mul_le_mul_of_nonneg_left (hS i hi) hn
    convert h using 1 <;> ring
  have hSum := sum_le_sum hPoint
  rw [sum_sub_distrib, ← mul_sum] at hSum
  have hConst : (∑ _i ∈ R n, β*δ n) = β*(δ n*((R n).card:ℝ)) := by simp; ring
  rw [hConst, ← mul_sum] at hSum
  have hP := mul_le_mul_of_nonneg_left hInv hα
  nlinarith only [hSum,hP,hηε,hc]

/-- Exact manuscript asymptotic J_* /(u sqrt n) = c_p/(18 P) in the limit. -/
theorem paper_retained_count_normalized
    (K v u : ℕ → ℝ) (R : ℕ → Finset ℕ) (P cp : ℝ)
    (hP : 0 < P) (hcp : 0 < cp)
    (hRatio : Tendsto (fun n ↦ ((R n).card:ℝ)/(K n*v n/18)) atTop (𝓝 (1/P)))
    (hScale : ∀ᶠ n in atTop, K n*v n = cp*(u n*Real.sqrt (n:ℝ)))
    (hPos : ∀ᶠ n in atTop, 0 < u n*Real.sqrt (n:ℝ)) :
    Tendsto (fun n ↦ ((R n).card:ℝ)/(u n*Real.sqrt (n:ℝ))) atTop (𝓝 (cp/(18*P))) := by
  have H := hRatio.const_mul (cp/18)
  have hh : cp/18*(1/P) = cp/(18*P) := by field_simp [hP.ne']
  rw [hh] at H
  apply H.congr'
  filter_upwards [hScale,hPos] with n hs hp
  change cp/18*(((R n).card:ℝ)/(K n*v n/18)) =
    ((R n).card:ℝ)/(u n*Real.sqrt (n:ℝ))
  rw [hs]
  let d := u n*Real.sqrt (n:ℝ)
  change cp/18*(((R n).card:ℝ)/(cp*d/18)) = ((R n).card:ℝ)/d
  field_simp [hcp.ne',show d≠0 from hp.ne']

theorem paper_retained_count_step_limit
    (K v : ℕ → ℝ) (R : ℕ → Finset ℕ) (P : ℝ) (hP : 0 < P)
    (hV : Tendsto (fun n ↦ K n*v n/18) atTop atTop)
    (hRatio : Tendsto (fun n ↦ ((R n).card:ℝ)/(K n*v n/18)) atTop (𝓝 (1/P))) :
    Tendsto (fun n ↦ (2*P/(K n*v n))*((R n).card:ℝ)) atTop (𝓝 (1/9)) := by
  have H := hRatio.const_mul (P/9)
  have hEq : P/9*(1/P) = 1/9 := by field_simp [hP.ne']
  rw [hEq] at H
  apply H.congr'
  filter_upwards [hV.eventually_gt_atTop 0] with n hn
  have hD : K n*v n ≠ 0 := by
    intro he
    rw [he,zero_div] at hn
    exact (lt_irrefl 0) hn
  change (P/9)*(((R n).card:ℝ)/(K n*v n/18)) = (2*P/(K n*v n))*((R n).card:ℝ)
  field_simp [hD] <;> ring

end CubeSqrtOverlap
#print axioms CubeSqrtOverlap.reinforced_first_sum_inverse_square
#print axioms CubeSqrtOverlap.paper_retained_count_normalized
#print axioms CubeSqrtOverlap.paper_retained_count_step_limit
