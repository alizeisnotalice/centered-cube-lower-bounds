import Mathlib.Algebra.Order.BigOperators.Group.Finset
import RetainedCountLimit
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

open Finset Filter
open scoped Topology
namespace CubeSqrtOverlap

theorem inverse_square_left_cell {x δ : ℝ} (hx : 0 < x) (hδ : 0 ≤ δ) :
    1/x - 1/(x+δ) ≤ δ/x^2 := by
  have hxδ : 0 < x+δ := add_pos_of_pos_of_nonneg hx hδ
  have he : 1/x-1/(x+δ) = δ/(x*(x+δ)) := by field_simp [hx.ne',hxδ.ne'] <;> ring
  rw [he]
  apply div_le_div_of_nonneg_left hδ (sq_pos_of_pos hx)
  rw [pow_two]
  exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hδ) hx.le

/-- Lower Riemann sum by an exact telescoping comparison; no generic
Riemann integrability infrastructure is needed for the inverse-square law. -/
theorem inverse_square_raw_grid_lower (a δ : ℝ) (ha : 0 < a) (hδ : 0 ≤ δ) (B : ℕ) :
    1/a - 1/(a+(B:ℝ)*δ) ≤ ∑ i ∈ range B, δ/(a+(i:ℝ)*δ)^2 := by
  induction B with
  | zero => simp
  | succ B ih =>
    rw [sum_range_succ]
    have hCell := inverse_square_left_cell
      (x:=a+(B:ℝ)*δ) (add_pos_of_pos_of_nonneg ha (by positivity)) hδ
    have hFn : a+((B+1:ℕ):ℝ)*δ = (a+(B:ℝ)*δ)+δ := by push_cast; ring
    rw [hFn]
    linarith only [ih,hCell]

theorem inverse_square_retained_grid_lower
    (a δ : ℝ) (ha : 0 < a) (hδ : 0 ≤ δ)
    (B : ℕ) (R : Finset ℕ) (hR : R ⊆ range B) :
    1/a - 1/(a+(B:ℝ)*δ) - δ*((range B \ R).card:ℝ)/a^2 ≤
      ∑ i ∈ R, δ/(a+(i:ℝ)*δ)^2 := by
  let f (i : ℕ) := δ/(a+(i:ℝ)*δ)^2
  have hCell (i : ℕ) : f i ≤ δ/a^2 := by
    unfold f
    apply div_le_div_of_nonneg_left hδ (sq_pos_of_pos ha)
    exact pow_le_pow_left₀ ha.le (le_add_of_nonneg_right (by positivity)) _
  have hD : (∑ i ∈ range B \ R, f i) ≤ δ*((range B \ R).card:ℝ)/a^2 := by
    calc
      _ ≤ ∑ _i ∈ range B \ R, δ/a^2 := sum_le_sum fun i _ ↦ hCell i
      _ = _ := by simp; ring
  have hS := Finset.sum_sdiff hR (f:=f)
  have hRaw := inverse_square_raw_grid_lower a δ ha hδ B
  change _ ≤ ∑ i ∈ range B, f i at hRaw
  change _ ≤ ∑ i ∈ R, f i
  linarith only [hD,hS,hRaw]

/-- The retained weighted grid converges from below to precisely (1/a−1/b),
with arbitrary eventual slack and a vanishing scaled deletion count. -/
theorem inverse_square_retained_lower_limit
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (δ : ℕ → ℝ) (B : ℕ → ℕ) (R : ℕ → Finset ℕ)
    (hδ : ∀ᶠ n in atTop, 0 ≤ δ n)
    (hR : ∀ᶠ n in atTop, R n ⊆ range (B n))
    (hEnd : Tendsto (fun n ↦ a+(B n:ℝ)*δ n) atTop (𝓝 b))
    (hD : Tendsto (fun n ↦ δ n*((range (B n) \ R n).card:ℝ)) atTop (𝓝 0))
    (ε : ℝ) (he : 0 < ε) :
    ∀ᶠ n in atTop, 1/a-1/b-ε ≤ ∑ i ∈ R n, δ n/(a+(i:ℝ)*δ n)^2 := by
  have hI : Tendsto (fun n ↦ 1/(a+(B n:ℝ)*δ n)) atTop (𝓝 (1/b)) :=
    tendsto_const_nhds.div hEnd hb.ne'
  have hA := (tendsto_const_nhds (x:=1/a)).sub hI
  have hE := hA.sub (hD.div_const (a^2))
  have hF : Tendsto (fun n ↦ 1/a-1/(a+(B n:ℝ)*δ n)-δ n*((range (B n) \ R n).card:ℝ)/a^2)
      atTop (𝓝 (1/a-1/b)) := by simpa only [zero_div,sub_zero] using hE
  filter_upwards [hδ,hR,hF.eventually_const_lt (sub_lt_self _ he)] with n hn hr hlim
  exact hlim.le.trans (inverse_square_retained_grid_lower a (δ n) ha hn (B n) (R n) hr)

end CubeSqrtOverlap
#print axioms CubeSqrtOverlap.inverse_square_retained_lower_limit
