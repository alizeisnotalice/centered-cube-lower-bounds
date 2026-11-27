import SqrtMidpointWeighted
import SqrtRawNearRepresentation
namespace CenteredCubeSqrt
open MeasureTheory Set
open scoped Interval BigOperators
set_option maxHeartbeats 1100000

theorem near_parabolic_integral (a : ℝ) :
    (∫ r in (0:ℝ)..a,r*(a-r))=a^3/6 := by
  have e (r : ℝ) : r*(a-r)=a*r-r^2 := by ring
  simp_rw [e]
  have i1 : IntervalIntegrable (fun r : ℝ => a*r) volume 0 a :=
    (continuous_id.const_mul a).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun r : ℝ => r^2) volume 0 a :=
    (continuous_id.pow 2).intervalIntegrable _ _
  rw [intervalIntegral.integral_sub i1 i2,intervalIntegral.integral_const_mul,integral_id,integral_pow]
  norm_num
  ring

theorem rawNearMain_exact_quantizer {B : ℕ} (hB : 0<B) {θ : ℝ} (hθ : θ∈Icc (0:ℝ) 1) :
    rawNearMain B θ=(1-θ)^3/6 +
      (∫ r in (0:ℝ)..(1-θ),actualMidpointPrefix B r) +
      (∫ r in (0:ℝ)..(1-θ),actualMidpointPrefix B (r+θ)) +
      (∫ r in (1-θ:ℝ)..1,midpointError B r*midpointError B (r+θ-1)) := by
  let a := 1-θ
  let E := midpointError B
  let P := actualMidpointPrefix B
  have ha : a∈Icc (0:ℝ) 1 := ⟨by dsimp [a]; linarith [hθ.2],by dsimp [a]; linarith [hθ.1]⟩
  have hA (y : Fin B) : IntervalIntegrable
      (fun r => cellPrimitive (labelCellMidpoint y) r*cellPrimitive (labelCellMidpoint y) (r+θ))
      volume 0 a := by
    exact labelCellPrimitive_prod_intervalIntegrable (y,y) ha.1 (by norm_num) ha.2
      (by simpa only [zero_add] using hθ.1) (by dsimp [a]; linarith)
  have hE1 : IntervalIntegrable (fun r => (a-r)*E r) volume 0 a :=
    (midpointError_all_intervalIntegrable hB 0 a).continuousOn_mul
      (continuous_const.sub continuous_id).continuousOn
  have iE2 : IntervalIntegrable (fun r => E (r+θ)) volume 0 a := by
    have h := (midpointError_all_intervalIntegrable hB (0+θ) (a+θ)).comp_add_right θ
    rwa [add_sub_cancel_right,add_sub_cancel_right] at h
  have hE2 : IntervalIntegrable (fun r => r*E (r+θ)) volume 0 a :=
    iE2.continuousOn_mul continuous_id.continuousOn
  have hPoly : IntervalIntegrable (fun r : ℝ => r*(a-r)) volume 0 a :=
    (continuous_id.mul (continuous_const.sub continuous_id)).intervalIntegrable _ _
  unfold rawNearMain rawCellMomentLeft rawCellMomentRight
  have hL : (1/(B:ℝ))*(∑ y : Fin B,∫ r in (0:ℝ)..a,
      cellPrimitive (labelCellMidpoint y) r*cellPrimitive (labelCellMidpoint y) (r+θ)) =
    ∫ r in (0:ℝ)..a,r*(a-r)+(a-r)*E r-r*E (r+θ) := by
    rw [←intervalIntegral.integral_finsetSum (fun y _ => hA y),←intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro r _
    dsimp only [a,E]
    rw [show 1-θ-r=1-r-θ by ring]
    exact same_label_pair_mean_exact hB r θ hθ.1
  have hR := rawCellUniformPair_moment (B:=B) hB (a:=a) (b:=1) (s:=θ-1)
    (by dsimp [a]; linarith [hθ.1]) ha.1 (by norm_num)
    (by dsimp [a]; linarith) (by linarith [hθ.2])
  simp_rw [←add_sub_assoc] at hR
  change (1/(B:ℝ))*(∑ y : Fin B,∫ r in (0:ℝ)..a,
      cellPrimitive (labelCellMidpoint y) r*cellPrimitive (labelCellMidpoint y) (r+θ)) +
    (1/(B:ℝ)^2)*(∑ p : Fin B×Fin B,∫ r in a..1,cellPrimitive (labelCellMidpoint p.1) r*
      cellPrimitive (labelCellMidpoint p.2) (r+θ-1)) = _
  rw [hL,hR,intervalIntegral.integral_sub (hPoly.add hE1) hE2,
    intervalIntegral.integral_add hPoly hE1,near_parabolic_integral,
    weighted_midpoint_left_exact hB ha]
  have he2 : -(∫ r in (0:ℝ)..a,r*E (r+θ)) = ∫ r in (0:ℝ)..a,P (r+θ) :=
    weighted_midpoint_right_exact hB hθ
  rw [sub_eq_add_neg,he2]

theorem rawNearMain_quantization_bound {B : ℕ} (hB : 0<B) {θ : ℝ} (hθ : θ∈Icc (0:ℝ) 1) :
    |rawNearMain B θ-(1-θ)^3/6|≤1/(4*(B:ℝ)^2) := by
  let a := 1-θ
  let c := 1/(8*(B:ℝ)^2)
  let P := actualMidpointPrefix B
  let E := midpointError B
  let L := ∫ r in (0:ℝ)..a,P r
  let U := ∫ r in (0:ℝ)..a,P (r+θ)
  let R := ∫ r in a..(1:ℝ),E r*E (r+θ-1)
  have ha : a∈Icc (0:ℝ) 1 := ⟨by dsimp [a]; linarith [hθ.2],by dsimp [a]; linarith [hθ.1]⟩
  have hP {r : ℝ} (hr : r∈Icc (0:ℝ) 1) : ‖P r‖≤c := by
    have e := actual_midpoint_prefix_bounds hB hr
    rw [Real.norm_eq_abs,abs_of_nonpos e.2]
    change -P r≤c
    have H : -c≤P r := e.1
    linarith
  have hL : |L|≤c*a := by
    unfold L
    rw [←Real.norm_eq_abs]
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (f:=P) (a:=0) (b:=a) (C:=c)
      (fun r hr => hP ⟨by rw [uIoc_of_le ha.1] at hr; exact hr.1.le,
        by rw [uIoc_of_le ha.1] at hr; exact hr.2.trans ha.2⟩)
    simpa only [sub_zero,abs_of_nonneg ha.1] using h
  have hU : |U|≤c*a := by
    unfold U
    rw [←Real.norm_eq_abs]
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (f:=fun r => P (r+θ)) (a:=0) (b:=a) (C:=c)
      (by
        intro r hr
        rw [uIoc_of_le ha.1] at hr
        exact hP ⟨by linarith [hr.1,hθ.1],by dsimp [a] at hr; linarith [hr.2]⟩)
    simpa only [sub_zero,abs_of_nonneg ha.1] using h
  have hR : |R|≤(1/(4*(B:ℝ)^2))*θ := by
    unfold R
    rw [←Real.norm_eq_abs]
    let D := 1/(2*(B:ℝ))
    have hD : 0≤D := by dsimp [D]; positivity
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (f:=fun r => E r*E (r+θ-1)) (a:=a) (b:=1) (C:=D^2) (by
        intro r hr
        rw [uIoc_of_le ha.2] at hr
        have hi : r∈Icc (0:ℝ) 1 := ⟨ha.1.trans hr.1.le,hr.2⟩
        have hi' : r+θ-1∈Icc (0:ℝ) 1 := ⟨by dsimp [a] at hr; linarith [hr.1],
          by linarith [hr.2,hθ.2]⟩
        rw [Real.norm_eq_abs,abs_mul,pow_two]
        exact mul_le_mul (midpointError_abs_le_half_cell hB hi)
          (midpointError_abs_le_half_cell hB hi') (abs_nonneg _) hD)
    have e : 1-a=θ := by dsimp [a]; ring
    rw [e,abs_of_nonneg hθ.1] at h
    have e' : D^2=1/(4*(B:ℝ)^2) := by unfold D; ring
    rwa [e'] at h
  have EE := rawNearMain_exact_quantizer hB hθ
  change rawNearMain B θ=a^3/6+L+U+R at EE
  rw [EE,show a^3/6+L+U+R-(1-θ)^3/6=(L+U)+R by dsimp [a]; ring]
  refine (abs_add_le _ _).trans ((add_le_add (abs_add_le L U) le_rfl).trans ?_)
  have e : c*a+c*a+(1/(4*(B:ℝ)^2))*θ=1/(4*(B:ℝ)^2) := by dsimp [c,a]; ring
  exact (add_le_add (add_le_add hL hU) hR).trans_eq e

#print axioms rawNearMain_quantization_bound
end CenteredCubeSqrt
