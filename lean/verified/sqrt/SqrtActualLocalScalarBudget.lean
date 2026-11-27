import SqrtActualLocalVariance
import Mathlib.Analysis.SpecificLimits.Basic

namespace CenteredCubeSqrt
open Set Filter MeasureTheory
open scoped Topology BigOperators
set_option maxHeartbeats 350000
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

noncomputable def actualLocalPulseBudget (B v e T s t : ℝ) (D : ℕ) : ℝ :=
  2*((2*(D:ℝ)+1)*(4*(2*T+e)/B^2)*(2*T)) +
  2*((2*(D:ℝ)+1)*(2/B)*(2*T)) + 4*(t-s)^2/v

noncomputable def actualLocalMainError (B K v e T s t : ℝ) (D : ℕ) : ℝ :=
  let P := actualLocalPulseBudget B v e T s t D
  let R := (29/3)*((16*localSpecConst+392)*T^2)/(K^2*v)
  (29/9)*P+(1/K)*((29/9)*(4*T+P))+(1+K)*R

theorem actualLocalMainError_tendsto {l : Filter ℕ} {B K v : ℕ→ℝ}
    (hB : Tendsto B l atTop) (hK : Tendsto K l atTop) (hv : Tendsto v l atTop)
    (e T s t : ℝ) (D : ℕ) :
    Tendsto (fun n => actualLocalMainError (B n) (K n) (v n) e T s t D) l (𝓝 0) := by
  have iB := tendsto_inv_atTop_zero.comp hB
  have iB2 := iB.pow 2
  have iK := tendsto_inv_atTop_zero.comp hK
  have iK2 := iK.pow 2
  have iv := tendsto_inv_atTop_zero.comp hv
  have p1 := iB2.const_mul (2*((2*(D:ℝ)+1)*(4*(2*T+e))*(2*T)))
  have p2 := iB.const_mul (2*((2*(D:ℝ)+1)*2*(2*T)))
  have p3 := iv.const_mul (4*(t-s)^2)
  have P : Tendsto (fun n => actualLocalPulseBudget (B n) (v n) e T s t D) l (𝓝 0) := by
    have H := (p1.add p2).add p3
    norm_num only [zero_pow,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,mul_zero,add_zero] at H
    apply H.congr
    intro n
    dsimp [Function.comp_def]
    unfold actualLocalPulseBudget
    simp only [div_eq_mul_inv,inv_pow]
    ring
  have r := ((iK2.add iK).mul iv).const_mul ((29/3)*((16*localSpecConst+392)*T^2))
  have r' : Tendsto (fun n =>
      (1+K n)*((29/3)*((16*localSpecConst+392)*T^2)/(K n^2*v n))) l (𝓝 0) := by
    norm_num only [zero_pow,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,mul_zero,add_zero] at r
    refine r.congr' ?_
    filter_upwards [hK.eventually_gt_atTop 0,hv.eventually_gt_atTop 0] with n a b
    dsimp [Function.comp_def]
    field_simp [a.ne',b.ne']
  have E := ((P.const_mul (29/9:ℝ)).add (iK.mul ((P.const_add (4*T)).const_mul (29/9)))).add r'
  unfold actualLocalMainError
  simpa only [Function.comp_def,one_div,mul_zero,zero_mul,zero_add,add_zero] using E

#print axioms actualLocalMainError_tendsto
end CenteredCubeSqrt
