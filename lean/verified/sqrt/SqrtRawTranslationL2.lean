import SqrtRawTranslationCounts
namespace CenteredCubeSqrt
open MeasureTheory Set
open scoped Interval BigOperators
set_option maxHeartbeats 900000

theorem actualRawWindow_measurable {B K : ℕ} [NeZero K] (f : ZMod K → Fin B) (L : ℝ) :
    Measurable (actualRawWindow f L) := by
  unfold actualRawWindow
  have h := actualRawPrimitive_measurable f
  exact (h.comp (measurable_id.add measurable_const)).sub (h.comp (measurable_id.sub measurable_const))

theorem actualRawWindow_periodic {B K : ℕ} [NeZero K] (f : ZMod K → Fin B) (L : ℝ) :
    Function.Periodic (actualRawWindow f L) 1 := by
  intro x
  unfold actualRawWindow
  rw [show x+1+L/2=(x+L/2)+1 by ring,show x+1-L/2=(x-L/2)+1 by ring,
    actualRawPrimitive_periodic f (x+L/2),actualRawPrimitive_periodic f (x-L/2)]

theorem actualRawWindow_abs_le_two {B K : ℕ} [NeZero K] (f : ZMod K → Fin B) (L x : ℝ) :
    |actualRawWindow f L x|≤2 := by
  unfold actualRawWindow
  have h := abs_add_le (actualRawPrimitive f (x+L/2)) (-actualRawPrimitive f (x-L/2))
  rw [←sub_eq_add_neg,abs_neg] at h
  exact h.trans (by linarith [actualRawPrimitive_abs_le_one f (x+L/2),actualRawPrimitive_abs_le_one f (x-L/2)])

theorem bounded_measurable_square_intervalIntegrable {F : ℝ→ℝ}
    (hF : Measurable F) {A : ℝ} (hA : ∀ x, |F x|≤A) (a b : ℝ) :
    IntervalIntegrable (fun x => (F x)^2) volume a b := by
  rw [intervalIntegrable_iff]
  apply Measure.integrableOn_of_bounded (M:=A^2) (s_finite:=by rw [uIoc]; simp [Real.volume_Ioc])
    (hF.pow_const 2).aestronglyMeasurable
  refine Filter.Eventually.of_forall ?_
  intro x
  change ‖(F x)^2‖ ≤ A^2
  rw [Real.norm_eq_abs,abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) (hA x) 2

theorem rawWindow_increment_square_integrable {B K : ℕ} [NeZero K] (f : ZMod K → Fin B)
    (L h a b : ℝ) : IntervalIntegrable
      (fun x => (actualRawWindow f L (x+h)-actualRawWindow f L x)^2) volume a b := by
  let W := actualRawWindow f L
  let F (x : ℝ) := W (x+h)-W x
  have hW : Measurable W := actualRawWindow_measurable f L
  have hM : Measurable F := (hW.comp (measurable_id.add measurable_const)).sub hW
  have hP (x : ℝ) : |W x|≤2 := actualRawWindow_abs_le_two f L x
  have hF (x : ℝ) : |F x|≤4 := by
    have hk := abs_add_le (W (x+h)) (-W x)
    rw [←sub_eq_add_neg,abs_neg] at hk
    exact hk.trans (by linarith [hP (x+h),hP x])
  exact bounded_measurable_square_intervalIntegrable hM hF a b

theorem rawWindow_forward_increment_L2 {B K : ℕ} [NeZero K]
    (f : ZMod K → Fin B) (L : ℝ) {h : ℝ} (hh : 0≤h) (hK : (K:ℝ)*h≤1) :
    (∫ x in (0:ℝ)..1, (actualRawWindow f L (x+h)-actualRawWindow f L x)^2) ≤ 4*(K:ℝ)*h := by
  let N (x : ℝ) := rawIntervalCount f h (x+L/2)
  let P (x : ℝ) := rawIntervalCount f h (x+ -(L/2))
  have hN : IntervalIntegrable N volume 0 1 := rawIntervalCount_integrable f h (L/2)
  have hP : IntervalIntegrable P volume 0 1 := rawIntervalCount_integrable f h (-(L/2))
  have e (x : ℝ) : (actualRawWindow f L (x+h)-actualRawWindow f L x)^2≤2*(N x+P x) := by
    rw [rawWindow_increment_count_identity,sub_eq_add_neg x (L/2)]
    have ha : 0≤N x ∧ N x≤2 := rawIntervalCount_bounded f hh hK (x+L/2)
    have hb : 0≤P x ∧ P x≤2 := rawIntervalCount_bounded f hh hK (x+ -(L/2))
    have hA := mul_le_mul_of_nonneg_left ha.2 ha.1
    have hB := mul_le_mul_of_nonneg_left hb.2 hb.1
    change (N x-P x)^2≤2*(N x+P x)
    nlinarith [mul_nonneg ha.1 hb.1]
  refine (intervalIntegral.integral_mono (by norm_num) (rawWindow_increment_square_integrable f L h 0 1)
    ((hN.add hP).const_mul 2) e).trans_eq ?_
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_add hN hP]
  change 2*((∫ x in (0:ℝ)..1,rawIntervalCount f h (x+L/2))+
    (∫ x in (0:ℝ)..1,rawIntervalCount f h (x+ -(L/2)))) = _
  rw [rawIntervalCount_period_integral,rawIntervalCount_period_integral]
  ring

theorem rawWindow_both_sign_increment_L2 {B K : ℕ} [NeZero K]
    (f : ZMod K → Fin B) (L h : ℝ) (hK : (K:ℝ)*|h|≤1) :
    (∫ x in (0:ℝ)..1, (actualRawWindow f L (x+h)-actualRawWindow f L x)^2) ≤ 4*(K:ℝ)*|h| := by
  rcases le_total 0 h with hh|hh
  · rw [abs_of_nonneg hh] at hK ⊢
    exact rawWindow_forward_increment_L2 f L hh hK
  · rw [abs_of_nonpos hh] at hK ⊢
    let W := actualRawWindow f L
    let G (x : ℝ) := (W (x+ -h)-W x)^2
    have hP : Function.Periodic W 1 := actualRawWindow_periodic f L
    have hG : Function.Periodic G 1 := by
      intro x
      unfold G
      rw [hP x,show x+1+ -h=(x+ -h)+1 by ring,hP (x+ -h)]
    have e (x : ℝ) : (W (x+h)-W x)^2=G (x+h) := by
      unfold G
      rw [add_neg_cancel_right,←neg_sub,neg_sq]
    change (∫ x in (0:ℝ)..1, (W (x+h)-W x)^2)≤4*(K:ℝ)*(-h)
    simp_rw [e]
    rw [intervalIntegral.integral_comp_add_right,zero_add,add_comm (1:ℝ),
      hG.intervalIntegral_add_eq h 0,zero_add]
    exact rawWindow_forward_increment_L2 f L (by linarith) hK

#print axioms rawWindow_both_sign_increment_L2
end CenteredCubeSqrt
