import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Filter
open scoped Topology
namespace CubeSqrtOverlap

theorem sqrt_log_over_rpow_tendsto_zero {a : ℝ} (ha : 0 < a) :
    Tendsto (fun x : ℝ ↦ Real.sqrt (Real.log x)/x^a) atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_atTop (show 0 < 2*a by positivity)).tendsto_div_nhds_zero
  have hS := Real.continuous_sqrt.continuousAt.tendsto.comp h
  rw [Real.sqrt_zero] at hS
  apply hS.congr'
  filter_upwards [eventually_ge_atTop (1:ℝ)] with x hx
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  change Real.sqrt (Real.log x/x^(2*a)) = _
  have he : x^(2*a) = (x^a)^2 := by rw [show 2*a=a+a by ring,Real.rpow_add hx0,pow_two]
  rw [he,Real.sqrt_div (Real.log_nonneg hx),Real.sqrt_sq (Real.rpow_pos_of_pos hx0 _).le]

/-- Direct mid/far rate for the actual paper prescription v≥16 log n,
v≤V log n and B≤K √(nv). -/
theorem retained_far_rate_tendsto_zero
    (B v : ℕ → ℝ) (V K : ℝ) (hK : 0 ≤ K) (hV : 0 ≤ V)
    (hB0 : ∀ᶠ n in atTop, 0 ≤ B n)
    (hvL : ∀ᶠ n : ℕ in atTop, 16*Real.log n ≤ v n)
    (hvU : ∀ᶠ n : ℕ in atTop, v n ≤ V*Real.log n)
    (hB : ∀ᶠ n : ℕ in atTop, B n ≤ K*Real.sqrt ((n:ℝ)*v n)) :
    Tendsto (fun n ↦ B n*Real.exp (-v n/25)) atTop (𝓝 0) := by
  have hl := (sqrt_log_over_rpow_tendsto_zero (a:=(7:ℝ)/50) (by norm_num)).comp
    (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hlim : Tendsto (fun n : ℕ ↦ (K*Real.sqrt V)*(Real.sqrt (Real.log n)/(n:ℝ)^((7:ℝ)/50)))
      atTop (𝓝 0) := by
    simpa only [mul_zero,Function.comp_apply] using hl.const_mul (K*Real.sqrt V)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
  · exact hB0.mono fun n hn ↦ mul_nonneg hn (Real.exp_pos _).le
  · filter_upwards [hB,hvL,hvU,eventually_ge_atTop (1:ℕ)] with n hBn hvl hvu hn
    have hnR : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    have hn0 : 0 < (n:ℝ) := zero_lt_one.trans_le hnR
    have hExp : Real.exp (-v n/25) ≤ (n:ℝ)^(-(16:ℝ)/25) := by
      rw [Real.rpow_def_of_pos hn0]
      exact Real.exp_le_exp.mpr (by linarith only [hvl])
    have hs : Real.sqrt ((n:ℝ)*v n) ≤ Real.sqrt (n:ℝ)*(Real.sqrt V*Real.sqrt (Real.log n)) := by
      rw [Real.sqrt_mul hn0.le,← Real.sqrt_mul hV]
      exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hvu) (Real.sqrt_nonneg _)
    have hBC := hBn.trans (mul_le_mul_of_nonneg_left hs hK)
    calc
      _ ≤ (K*(Real.sqrt (n:ℝ)*(Real.sqrt V*Real.sqrt (Real.log n))))*((n:ℝ)^(-(16:ℝ)/25)) :=
        mul_le_mul hBC hExp (Real.exp_pos _).le (by positivity)
      _ = (K*Real.sqrt V)*(Real.sqrt (Real.log n)/(n:ℝ)^((7:ℝ)/50)) := by
        have he : Real.sqrt (n:ℝ)*((n:ℝ)^(-(16:ℝ)/25)) = ((n:ℝ)^((7:ℝ)/50))⁻¹ := by
          rw [Real.sqrt_eq_rpow,← Real.rpow_add hn0,← Real.rpow_neg hn0.le]
          norm_num
        rw [show (K*(Real.sqrt (n:ℝ)*(Real.sqrt V*Real.sqrt (Real.log n))))*((n:ℝ)^(-(16:ℝ)/25)) =
          (K*Real.sqrt V)*(Real.sqrt (Real.log n)*(Real.sqrt (n:ℝ)*((n:ℝ)^(-(16:ℝ)/25)))) by ring,he]
        simp only [div_eq_mul_inv]

end CubeSqrtOverlap
#print axioms CubeSqrtOverlap.retained_far_rate_tendsto_zero
