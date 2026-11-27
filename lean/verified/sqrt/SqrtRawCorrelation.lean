import SqrtRawPrimitive

namespace CenteredCubeSqrt
open MeasureTheory Set
open scoped Interval BigOperators
set_option maxHeartbeats 1800000

noncomputable def rawCorrelation {B K : ℕ} [NeZero K] (f : ZMod K → Fin B) (z : ℝ) :=
  ∫ x in (0:ℝ)..1, actualRawPrimitive f x*actualRawPrimitive f (x+z/(K:ℝ))

noncomputable def rawCellMomentLeft {B : ℕ} (θ : ℝ) (p : Fin B × Fin B) :=
  ∫ r in (0:ℝ)..(1-θ), cellPrimitive (labelCellMidpoint p.1) r * cellPrimitive (labelCellMidpoint p.2) (r+θ)

noncomputable def rawCellMomentRight {B : ℕ} (θ : ℝ) (p : Fin B × Fin B) :=
  ∫ r in (1-θ:ℝ)..1, cellPrimitive (labelCellMidpoint p.1) r * cellPrimitive (labelCellMidpoint p.2) (r+θ-1)

theorem actualRawPrimitive_mul_intervalIntegrable {B K : ℕ} [NeZero K]
    (f : ZMod K → Fin B) (s a b : ℝ) :
    IntervalIntegrable (fun r => actualRawPrimitive f r*actualRawPrimitive f (r+s)) volume a b := by
  have hm := actualRawPrimitive_measurable f
  have hM : Measurable (fun r => actualRawPrimitive f r*actualRawPrimitive f (r+s)) :=
    hm.mul (hm.comp (measurable_id.add measurable_const))
  rw [intervalIntegrable_iff]
  apply Measure.integrableOn_of_bounded (M:=1) (s_finite:=by rw [uIoc]; simp [Real.volume_Ioc])
    hM.aestronglyMeasurable
  refine Filter.Eventually.of_forall ?_
  intro r
  rw [Real.norm_eq_abs,abs_mul]
  exact (mul_le_of_le_one_right (abs_nonneg _) (actualRawPrimitive_abs_le_one f (r+s))).trans
    (actualRawPrimitive_abs_le_one f r)

theorem rawCorrelation_cell_decomp {B K : ℕ} [NeZero K] (f : ZMod K → Fin B)
    (k : ℤ) {θ : ℝ} (hθ : θ∈Icc (0:ℝ) 1) :
    rawCorrelation f ((k:ℝ)+θ) = (1/(K:ℝ)) * (∑ j ∈ Finset.range K,
      (rawCellMomentLeft θ (f (j:ZMod K),f ((j:ZMod K)+(k:ZMod K)))+
      rawCellMomentRight θ (f (j:ZMod K),f ((j:ZMod K)+(k:ZMod K)+1)))) := by
  let c := (1:ℝ)/(K:ℝ)
  let s := ((k:ℝ)+θ)/(K:ℝ)
  let F (r : ℝ) := actualRawPrimitive f r*actualRawPrimitive f (r+s)
  have hK : (K:ℝ)≠0 := by exact_mod_cast (NeZero.ne K)
  have hc : 0<c := by
    unfold c
    have hh : (0:ℝ)<K := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne K)
    positivity
  have hFull := intervalIntegral.sum_integral_adjacent_intervals (f:=F) (a:=fun j : ℕ => (j:ℝ)/(K:ℝ))
    (n:=K) (fun j _ => actualRawPrimitive_mul_intervalIntegrable f s _ _)
  rw [Nat.cast_zero,zero_div,div_self hK] at hFull
  change (∫ x in (0:ℝ)..1,F x)=_
  rw [←hFull]
  change _ = c * _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  let G (r : ℝ) := F (c*r+(j:ℝ)/(K:ℝ))
  have e := intervalIntegral.smul_integral_comp_mul_add F (a:=0) (b:=1) c ((j:ℝ)/(K:ℝ))
  rw [mul_zero,zero_add,mul_one,show c+(j:ℝ)/(K:ℝ)=((j+1:ℕ):ℝ)/(K:ℝ) by unfold c; push_cast; ring,
    smul_eq_mul] at e
  rw [←e]
  change c*(∫ r in (0:ℝ)..1,G r)=c*_
  congr 1
  have hI (a b : ℝ) : IntervalIntegrable G volume a b := by
    have hh := ((actualRawPrimitive_mul_intervalIntegrable f s (c*a+(j:ℝ)/(K:ℝ))
      (c*b+(j:ℝ)/(K:ℝ))).comp_add_right ((j:ℝ)/(K:ℝ))).comp_mul_left (c:=c)
    rwa [add_sub_cancel_right,add_sub_cancel_right,mul_div_cancel_left₀ a hc.ne',
      mul_div_cancel_left₀ b hc.ne'] at hh
  rw [←intervalIntegral.integral_add_adjacent_intervals (hI 0 (1-θ)) (hI (1-θ) 1)]
  unfold rawCellMomentLeft rawCellMomentRight
  congr 1
  · apply intervalIntegral.integral_congr_Ioo_of_le (by linarith [hθ.2])
    intro r hr
    have h1 : r∈Ico (0:ℝ) 1 := ⟨hr.1.le,by linarith [hr.2,hθ.1]⟩
    have h2 : r+θ∈Ico (0:ℝ) 1 := ⟨by linarith [hr.1,hθ.1],by linarith [hr.2]⟩
    unfold G F c s
    have e1 : 1/(K:ℝ)*r+(j:ℝ)/(K:ℝ)=(((j:ℤ):ℝ)+r)/(K:ℝ) := by push_cast; ring
    have e2 : (((j:ℤ):ℝ)+r)/(K:ℝ)+((k:ℝ)+θ)/(K:ℝ)=
        ((((j:ℤ)+k:ℤ):ℝ)+(r+θ))/(K:ℝ) := by push_cast; ring
    rw [e1,e2,actualRawPrimitive_in_cell f (j:ℤ) h1,actualRawPrimitive_in_cell f ((j:ℤ)+k) h2]
    push_cast
    rfl
  · apply intervalIntegral.integral_congr_Ioo_of_le (by linarith [hθ.1])
    intro r hr
    have h1 : r∈Ico (0:ℝ) 1 := ⟨by linarith [hr.1,hθ.2],hr.2⟩
    have h2 : r+θ-1∈Ico (0:ℝ) 1 := ⟨by linarith [hr.1],by linarith [hr.2,hθ.2]⟩
    unfold G F c s
    have e1 : 1/(K:ℝ)*r+(j:ℝ)/(K:ℝ)=(((j:ℤ):ℝ)+r)/(K:ℝ) := by push_cast; ring
    have e2 : (((j:ℤ):ℝ)+r)/(K:ℝ)+((k:ℝ)+θ)/(K:ℝ)=
        ((((j:ℤ)+k+1:ℤ):ℝ)+(r+θ-1))/(K:ℝ) := by push_cast; ring
    rw [e1,e2,actualRawPrimitive_in_cell f (j:ℤ) h1,actualRawPrimitive_in_cell f ((j:ℤ)+k+1) h2]
    push_cast
    rfl

#print axioms rawCorrelation_cell_decomp
end CenteredCubeSqrt
