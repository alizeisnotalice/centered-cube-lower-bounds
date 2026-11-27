import SqrtMidpointPrefix
namespace CenteredCubeSqrt
open MeasureTheory Set
open scoped Interval BigOperators
set_option maxHeartbeats 1000000

noncomputable def actualMidpointPrefix (B : ℕ) (x : ℝ) := ∫ y in (0:ℝ)..x,midpointError B y

theorem midpointError_grid_prefix_zero {B j : ℕ} (hj : j≤B) :
    actualMidpointPrefix B ((j:ℝ)/(B:ℝ))=0 := by
  have hI (k : ℕ) (hk : k<j) :
      IntervalIntegrable (midpointError B) volume ((k:ℝ)/(B:ℝ)) (((k+1:ℕ):ℝ)/(B:ℝ)) := by
    simpa only [pow_one] using midpointError_cell_power_integrable (hk.trans_le hj) 1
  have h := intervalIntegral.sum_integral_adjacent_intervals (f:=midpointError B)
    (a:=fun k : ℕ => (k:ℝ)/(B:ℝ)) hI
  rw [Nat.cast_zero,zero_div] at h
  unfold actualMidpointPrefix
  rw [←h]
  apply Finset.sum_eq_zero
  intro k hk
  have hk' : k<B := (Finset.mem_range.mp hk).trans_le hj
  have H := midpointError_cell_power_integral hk' 1
  simpa only [pow_one,scaledMidpointError_mean_zero hk',mul_zero] using H

theorem midpointError_normalized_prefix {B j : ℕ} (hj : j<B) {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    actualMidpointPrefix B (((j:ℝ)+t)/(B:ℝ)) =
    (1/(B:ℝ))*(∫ y in (0:ℝ)..t,scaledMidpointError B j y) := by
  let a := (j:ℝ)/(B:ℝ)
  let b := ((j:ℝ)+t)/(B:ℝ)
  have hB0 : 0<(B:ℝ) := by exact_mod_cast (show 0<B by omega)
  have ha : 0≤a := by dsimp [a]; positivity
  have hb : b≤1 := by
    dsimp [b]
    apply (div_le_one hB0).mpr
    have h : (j:ℝ)+1≤B := by exact_mod_cast Nat.succ_le_of_lt hj
    linarith [ht.2]
  have hab : a≤b := by dsimp [a,b]; exact div_le_div_of_nonneg_right (by linarith [ht.1]) hB0.le
  have hf (l u : ℝ) (hlu : l≤u) (hl : 0≤l) (hu : u≤1) :
      IntervalIntegrable (midpointError B) volume l u := by
    rw [intervalIntegrable_iff,uIoc_of_le hlu]
    apply Measure.integrableOn_of_bounded (M:=1) (s_finite:=by simp [Real.volume_Ioc])
      (midpointError_measurable (show 0<B by omega)).aestronglyMeasurable
    filter_upwards [ae_restrict_mem (μ:=volume) measurableSet_Ioc] with x hx
    rw [Real.norm_eq_abs]
    exact midpointError_abs_le_one (show 0<B by omega) ⟨hl.trans hx.1.le,hx.2.trans hu⟩
  have adj := intervalIntegral.integral_add_adjacent_intervals (hf 0 a ha (by norm_num) (hab.trans hb))
    (hf a b hab ha hb)
  have hp : (∫ y in (0:ℝ)..a,midpointError B y)=0 :=
    midpointError_grid_prefix_zero hj.le
  rw [hp,zero_add] at adj
  change (∫ y in (0:ℝ)..b,midpointError B y)=_
  rw [←adj]
  let c := (1:ℝ)/(B:ℝ)
  have hi := intervalIntegral.smul_integral_comp_mul_add (midpointError B) (a:=0) (b:=t) c a
  have e (y : ℝ) : c*y+a=((j:ℝ)+y)/(B:ℝ) := by dsimp [c,a]; ring
  simp_rw [e] at hi
  simpa only [add_zero,smul_eq_mul,c,scaledMidpointError,b,a] using hi.symm

theorem actual_midpoint_prefix_bounds {B : ℕ} (hB : 0<B) {x : ℝ} (hx : x∈Icc (0:ℝ) 1) :
    -(1/(8*(B:ℝ)^2))≤actualMidpointPrefix B x ∧ actualMidpointPrefix B x≤0 := by
  have hB0 : 0<(B:ℝ) := by exact_mod_cast hB
  rcases lt_or_eq_of_le hx.2 with hx1|hx1
  · let k : ℤ := ⌊(B:ℝ)*x⌋
    let j := k.toNat
    have hkn : 0≤k := Int.floor_nonneg.mpr (mul_nonneg hB0.le hx.1)
    have hc : (j:ℤ)=k := Int.toNat_of_nonneg hkn
    have hcr : (j:ℝ)=(k:ℝ) := by exact_mod_cast hc
    have hj : j<B := by
      have h : (j:ℝ)<(B:ℝ) := by
        rw [hcr]
        exact (Int.floor_le ((B:ℝ)*x)).trans_lt (by nlinarith [mul_lt_mul_of_pos_left hx1 hB0])
      exact_mod_cast h
    let t := (B:ℝ)*x-(j:ℝ)
    have htl : x=((j:ℝ)+t)/(B:ℝ) := by dsimp [t]; field_simp; ring
    have ht : t∈Icc (0:ℝ) 1 := by
      dsimp only [t]
      rw [hcr]
      exact ⟨by linarith [Int.floor_le ((B:ℝ)*x)],
        by linarith [Int.lt_floor_add_one ((B:ℝ)*x)]⟩
    rw [htl,midpointError_normalized_prefix hj ht]
    have h := scaledMidpointError_prefix_abs_bound hj ht
    constructor
    · have h' := mul_le_mul_of_nonneg_left h.1 (one_div_nonneg.mpr hB0.le)
      exact (show -(1/(8*(B:ℝ)^2))=(1/(B:ℝ))* (-(1/(8*(B:ℝ)))) by ring) ▸ h'
    · exact mul_nonpos_of_nonneg_of_nonpos (one_div_nonneg.mpr hB0.le) h.2
  · subst x
    have h := midpointError_grid_prefix_zero (B:=B) (j:=B) le_rfl
    rw [div_self hB0.ne'] at h
    rw [h]
    exact ⟨neg_nonpos.mpr (by positivity),le_rfl⟩

#print axioms actual_midpoint_prefix_bounds
end CenteredCubeSqrt
