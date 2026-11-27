import WalshPrimitiveStep
import WalshDiscreteEnergy

namespace CenteredCubeSqrt
open MeasureTheory Set Classical
open scoped Interval BigOperators
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem ordinalWalsh_abs {b : ℕ} (a : NonzeroBinary b) (y : Fin (2^b)) :
    |ordinalWalsh a y|=1 := by
  unfold ordinalWalsh bitCharacter
  rw [abs_pow]
  norm_num

theorem walshCellPrimitive_abs_le_one {b : ℕ} (a : NonzeroBinary b) (r : ℝ) :
    |walshCellPrimitive a r|≤1 := by
  rw [walshCellPrimitive_eq_count,abs_div,abs_of_pos (by positivity : 0<(2:ℝ)^b),
      div_le_one (by positivity : 0<(2:ℝ)^b)]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have H : ∀ y : Fin (2^b), |(if labelCellMidpoint y ≤ r then ordinalWalsh a y else 0)| ≤ 1 := by
    intro y
    split <;> simp [ordinalWalsh_abs]
  refine (Finset.sum_le_sum (fun y _ => H y)).trans_eq ?_
  simp

theorem walshPrimitive_pow_intervalIntegrable {b : ℕ} (a : NonzeroBinary b) (l r : ℝ) :
    IntervalIntegrable (fun t => (walshCellPrimitive a t)^2) volume l r := by
  rw [intervalIntegrable_iff]
  apply Measure.integrableOn_of_bounded (M:=1) (s_finite:=by simp [Real.volume_uIoc])
    ((walshCellPrimitive_measurable a).pow_const 2).aestronglyMeasurable
  filter_upwards with t
  simp only [Real.norm_eq_abs,abs_pow]
  simpa using pow_le_pow_left₀ (abs_nonneg _) (walshCellPrimitive_abs_le_one a t) 2

theorem walshThreshold_mono (b : ℕ) : StrictMono (walshThreshold b) := by
  intro j k h
  unfold walshThreshold
  apply div_lt_div_of_pos_right _ (by positivity)
  have H : (j:ℝ) < k := by exact_mod_cast h
  linarith

theorem walsh_integral_step {b : ℕ} (a : NonzeroBinary b) (j : ℕ) (hj : j<2^b) :
    (∫ t in walshThreshold b j..walshThreshold b (j+1), (walshCellPrimitive a t)^2) =
      (walshPrefix a.1 (j+1))^2 / ((2:ℝ)^b)^3 := by
  let c := (walshPrefix a.1 (j+1)/(2:ℝ)^b)^2
  have e : (∫ t in walshThreshold b j..walshThreshold b (j+1), (walshCellPrimitive a t)^2) =
      ∫ _ in walshThreshold b j..walshThreshold b (j+1), c := by
    apply intervalIntegral.integral_congr_ae'
    · have he : ∀ᵐ t ∂(volume:Measure ℝ), t ≠ walshThreshold b (j+1) := by rw [ae_iff]; simpa using (measure_singleton (walshThreshold b (j+1)) (μ := (volume : Measure ℝ)))
      filter_upwards [he] with t ht hm
      exact congrArg (fun x : ℝ => x^2) (walshCellPrimitive_mid_step a t j hj ⟨hm.1.le,lt_of_le_of_ne hm.2 ht⟩)
    · filter_upwards with t hm
      exact (not_lt_of_ge ((walshThreshold_mono b) (Nat.lt_succ_self j)).le (hm.1.trans_le hm.2)).elim
  rw [e, intervalIntegral.integral_const, smul_eq_mul]
  have hz : (2:ℝ)^b ≠ 0 := pow_ne_zero _ (by norm_num)
  unfold c walshThreshold
  push_cast
  field_simp
  ring

theorem walsh_energy_first_interval {b : ℕ} (a : NonzeroBinary b) :
    (∫ t in (0:ℝ)..walshThreshold b 0, (walshCellPrimitive a t)^2) = 0 := by
  rw [intervalIntegral.integral_of_le (by unfold walshThreshold; positivity)]
  have z : (fun t : ℝ => (walshCellPrimitive a t)^2) =ᵐ[volume.restrict (Ioc 0 (walshThreshold b 0))]
      (fun _ => 0) := by
    have he : ∀ᵐ t ∂(volume:Measure ℝ), t ≠ walshThreshold b 0 := by rw [ae_iff]; simpa using (measure_singleton (walshThreshold b 0) (μ := (volume : Measure ℝ)))
    filter_upwards [ae_restrict_mem (μ:=volume) measurableSet_Ioc,
      ae_restrict_of_ae he] with t ht htne
    rw [walshCellPrimitive_from_cut a t 0 (Nat.zero_le _) (by
      intro k _
      have hT := (walshThreshold_mono b).monotone (Nat.zero_le k)
      have hlt := lt_of_le_of_ne ht.2 htne
      simp [not_le_of_gt (hlt.trans_le hT)]),walshPrefix]
    simp
  rw [integral_congr_ae z, integral_zero]

theorem walsh_energy_last_interval {b : ℕ} (a : NonzeroBinary b) :
    (∫ t in (1:ℝ)..walshThreshold b (2^b), (walshCellPrimitive a t)^2) = 0 := by
  have HT : 1≤walshThreshold b (2^b) := by
    unfold walshThreshold
    push_cast
    exact (le_div_iff₀ (by positivity : 0<(2:ℝ)^b)).mpr (by linarith)
  rw [intervalIntegral.integral_of_le HT]
  have z : (fun t : ℝ => (walshCellPrimitive a t)^2) =ᵐ[volume.restrict (Ioc 1 (walshThreshold b (2^b)))]
      (fun _ => 0) := by
    filter_upwards [ae_restrict_mem (μ:=volume) measurableSet_Ioc] with t ht
    rw [walshCellPrimitive_from_cut a t (2^b) le_rfl (by
      intro k hk
      have kreal : (k:ℝ)+1≤(2:ℝ)^b := by exact_mod_cast hk
      have hle : walshThreshold b k ≤ 1 := by
        unfold walshThreshold
        exact (div_le_iff₀ (by positivity : 0<(2:ℝ)^b)).mpr (by linarith)
      simp [hk, hle.trans ht.1.le]), walshPrefix_end_zero_of_nonzero _ a.2]
    simp
  rw [integral_congr_ae z, integral_zero]

theorem walsh_primitive_energy_exact {b : ℕ} (a : NonzeroBinary b) :
    (∫ t in (0:ℝ)..1, (walshCellPrimitive a t)^2) =
     (walshRun b a.1 : ℝ)^2/(3*((2:ℝ)^b)^2) + 1/(6*((2:ℝ)^b)^2) := by
  let f (t : ℝ) := (walshCellPrimitive a t)^2
  have h := intervalIntegral.sum_integral_adjacent_intervals (f:=f)
    (a:=walshThreshold b) (n:=2^b) (fun j _ => walshPrimitive_pow_intervalIntegrable a _ _)
  have h' := intervalIntegral.integral_add_adjacent_intervals
     (walshPrimitive_pow_intervalIntegrable a 0 (walshThreshold b 0))
     (walshPrimitive_pow_intervalIntegrable a (walshThreshold b 0) (walshThreshold b (2^b)))
  have h'' := intervalIntegral.integral_add_adjacent_intervals
     (walshPrimitive_pow_intervalIntegrable a 0 1)
     (walshPrimitive_pow_intervalIntegrable a 1 (walshThreshold b (2^b)))
  rw [walsh_energy_first_interval,zero_add] at h'
  rw [walsh_energy_last_interval,add_zero] at h''
  rw [h'', ←h', ←h]
  have hm : (∑ j ∈ Finset.range (2^b), ∫ t in walshThreshold b j..walshThreshold b (j+1), f t) =
    ∑ j ∈ Finset.range (2^b), (walshPrefix a.1 (j+1))^2 / ((2:ℝ)^b)^3 := by
    apply Finset.sum_congr rfl
    intro j hj
    exact walsh_integral_step a j (Finset.mem_range.mp hj)
  rw [hm,←Finset.sum_div]
  have he := Finset.sum_range_succ' (fun j => (walshPrefix a.1 j)^2) (2^b)
  rw [Finset.sum_range_succ,walshPrefix_end_zero_of_nonzero _ a.2] at he
  have hp : walshPrefix a.1 0 = 0 := by simp [walshPrefix]
  rw [hp] at he
  simp only [zero_pow (by decide : 2 ≠ 0),add_zero] at he
  rw [←he]
  change walshDiscreteEnergy a.1 / ((2:ℝ)^b)^3 = _
  rw [walshDiscreteEnergy_exact _ a.2]
  have hz : (2:ℝ)^b ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp

#print axioms walsh_primitive_energy_exact
end CenteredCubeSqrt
