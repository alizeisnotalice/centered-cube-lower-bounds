import PeriodicHaloTransferSqrt
import SqrtActualWindowCentered
import SqrtPeriodicBoxHarmonic
import Mathlib.Analysis.Real.Pi.Bounds

open MeasureTheory Set
open scoped BigOperators Interval ENNReal
namespace CenteredCubeSqrt

theorem actualLowDensity_periodic (M : ℕ) :
    Function.Periodic (actualLowDensity M) 1 := by
  intro x
  unfold actualLowDensity
  apply Finset.sum_congr rfl
  intro m _
  have h := cosine_integer_harmonic_periodic (m+1) x
  have hc : ((m:ℝ)+1)*(2*Real.pi) = 2*Real.pi*((m+1:ℕ):ℝ) := by push_cast; ring
  rw [hc]
  exact congrArg (fun z => Real.pi*((m:ℝ)+1)*lowSpectrumAmp m*z) h

theorem actualLowDensity_unit_mass (M : ℕ) :
    (∫ x in (0:ℝ)..1, actualLowDensity M x) = 0 := by
  unfold actualLowDensity
  rw [intervalIntegral.integral_finsetSum]
  · simp_rw [intervalIntegral.integral_const_mul, integral_cos_n_period, mul_zero, Finset.sum_const_zero]
  · intro m _
    apply Continuous.intervalIntegrable
    fun_prop

theorem actualWitnessDensity_intervalIntegrable {B K : ℕ} [NeZero K]
    (f : ZMod K → Fin B) (M : ℕ) (p δ : ℝ) (hδ : 0 < δ) (a b : ℝ) :
    IntervalIntegrable (actualWitnessDensity f M p δ) volume a b := by
  unfold actualWitnessDensity
  exact (intervalIntegrable_const.add
    ((atomBoxSum_intervalIntegrable f hδ a b).const_mul _)).add
      (((actualLowDensity_continuous M).intervalIntegrable a b).const_mul _)

theorem actualWitnessDensity_periodic {B K : ℕ} [NeZero K]
    (f : ZMod K → Fin B) (M : ℕ) (p δ : ℝ) :
    Function.Periodic (actualWitnessDensity f M p δ) 1 := by
  intro x
  unfold actualWitnessDensity
  change 1 - p + (p/(K:ℝ))*atomBoxSum f δ (x+1) + (p/(K:ℝ))*actualLowDensity M (x+1) =
    1 - p + (p/(K:ℝ))*atomBoxSum f δ x + (p/(K:ℝ))*actualLowDensity M x
  rw [atomBoxSum_periodic f δ x, actualLowDensity_periodic M x]

theorem actualWitnessDensity_unit_mass {B K : ℕ} [NeZero K]
    (f : ZMod K → Fin B) (M : ℕ) (p δ : ℝ) (hB : 0 < B) (hK : 2 ≤ K) (hδ : 0 < δ)
    (hsmall : δ < 1 / ((B:ℝ)*(K:ℝ))) :
    (∫ x in (0:ℝ)..1, actualWitnessDensity f M p δ x) = 1 := by
  have hA := (atomBoxSum_intervalIntegrable f hδ 0 1).const_mul (p/(K:ℝ))
  have hL := ((actualLowDensity_continuous M).intervalIntegrable (μ := volume) 0 1).const_mul (p/(K:ℝ))
  change (∫ x in (0:ℝ)..1, 1 - p + (p/(K:ℝ))*atomBoxSum f δ x +
      (p/(K:ℝ))*actualLowDensity M x) = 1
  rw [intervalIntegral.integral_add (intervalIntegrable_const.add hA) hL,
    intervalIntegral.integral_add intervalIntegrable_const hA,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    atomBoxSum_period_integral f hB hK hδ hsmall, actualLowDensity_unit_mass,
    intervalIntegral.integral_const]
  have hk : (K:ℝ) ≠ 0 := by exact_mod_cast NeZero.ne K
  simp [hk]

theorem actualWitnessDensity_positive {B K : ℕ} [NeZero K]
    (f : ZMod K → Fin B) (M : ℕ) {p δ : ℝ} (hp : 0 ≤ p) (_hp1 : p < 1) (hδ : 0 < δ)
    (hLow : ∀ x, |(p/(K:ℝ))*actualLowDensity M x| ≤ (1-p)/2) (x : ℝ) :
    (1-p)/2 ≤ actualWitnessDensity f M p δ x := by
  have hA : 0 ≤ (p/(K:ℝ))*atomBoxSum f δ x :=
    mul_nonneg (div_nonneg hp (Nat.cast_nonneg K)) (atomBoxSum_nonneg f hδ x)
  have hL : -(1-p)/2 ≤ (p/(K:ℝ))*actualLowDensity M x := by
    linarith [(abs_le.mp (hLow x)).1]
  unfold actualWitnessDensity
  change (1-p)/2 ≤ 1-p+(p/(K:ℝ))*atomBoxSum f δ x+(p/(K:ℝ))*actualLowDensity M x
  linarith

theorem actualLowDensity_coarse_bound (M : ℕ) (x : ℝ) :
    |actualLowDensity M x| ≤ 9 * (M:ℝ) := by
  unfold actualLowDensity
  calc
    _ ≤ ∑ m ∈ Finset.range M, |Real.pi*((m:ℝ)+1)*lowSpectrumAmp m *
        Real.cos (((m:ℝ)+1)*(2*Real.pi)*x)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _m ∈ Finset.range M, (9:ℝ) := by
      apply Finset.sum_le_sum
      intro m _
      let a : ℝ := (m:ℝ)+1
      have ha : 0 < a := by dsimp [a]; positivity
      have ha1 : 1 ≤ a := by dsimp [a]; linarith [Nat.cast_nonneg (α := ℝ) m]
      have hamp : lowSpectrumAmp m < 20/(9*a^2) := plateauCoeff_amplitude a ha
      have hp : Real.pi ≤ 4 := le_of_lt (Real.pi_lt_d20.trans (by norm_num))
      have hb : 0 ≤ lowSpectrumAmp m := Real.sqrt_nonneg _
      rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ Real.pi*((m:ℝ)+1)*lowSpectrumAmp m)]
      calc
        _ ≤ Real.pi*a*lowSpectrumAmp m := mul_le_of_le_one_right (by positivity) (Real.abs_cos_le_one _)
        _ ≤ 4*a*(20/(9*a^2)) := by gcongr
        _ = (80/9)/a := by field_simp; ring
        _ ≤ 9 := (div_le_iff₀ ha).2 (by linarith)
    _ = _ := by simp [mul_comm]

theorem actualWitnessDensity_positive_of_coarse {B K : ℕ} [NeZero K]
    (f : ZMod K → Fin B) (M : ℕ) {p δ : ℝ} (hp : 0 ≤ p) (hp1 : p < 1) (hδ : 0 < δ)
    (hc : (p/(K:ℝ)) * (9*(M:ℝ)) ≤ (1-p)/2) (x : ℝ) :
    (1-p)/2 ≤ actualWitnessDensity f M p δ x := by
  apply actualWitnessDensity_positive f M hp hp1 hδ (fun y => ?_) x
  rw [abs_mul, abs_of_nonneg (div_nonneg hp (Nat.cast_nonneg K))]
  exact (mul_le_mul_of_nonneg_left (actualLowDensity_coarse_bound M y)
    (div_nonneg hp (Nat.cast_nonneg K))).trans hc

theorem actual_intervalSource_eq_perturbation {B K : ℕ} [NeZero K]
    (f : ZMod K → Fin B) (M : ℕ) (p δ L x : ℝ) :
    CenteredCube.intervalSource (actualWitnessDensity f M p δ) L x =
      1 + actualWindowPerturbation f M p δ L x := by
  unfold CenteredCube.intervalSource actualWindowPerturbation
  rw [one_div, div_eq_mul_inv, mul_comm]
  ring

theorem actual_intervalSource_positive {B K : ℕ} [NeZero K]
    (f : ZMod K → Fin B) (M : ℕ) {p δ L : ℝ} (hp : 0 ≤ p) (hp1 : p < 1)
    (hδ : 0 < δ) (hL : 0 < L) (hc : (p/(K:ℝ)) * (9*(M:ℝ)) ≤ (1-p)/2) (x : ℝ) :
    0 < CenteredCube.intervalSource (actualWitnessDensity f M p δ) L x := by
  have h := intervalIntegral.integral_mono_on (μ := volume)
    (a := x-L/2) (b := x+L/2) (by linarith : x-L/2 ≤ x+L/2)
    (intervalIntegrable_const (c := (1-p)/2))
    (actualWitnessDensity_intervalIntegrable f M p δ hδ _ _)
    (fun y _ => actualWitnessDensity_positive_of_coarse f M hp hp1 hδ hc y)
  rw [intervalIntegral.integral_const, smul_eq_mul, show x+L/2-(x-L/2) = L by ring] at h
  unfold CenteredCube.intervalSource
  exact mul_pos (one_div_pos.2 hL)
    ((mul_pos hL (by linarith : 0 < (1-p)/2)).trans_le h)

theorem weakConstant_ge_actual_witness_iid_event {B K n : ℕ} [NeZero K]
    (f : ZMod K → Fin B) (M : ℕ) {p δ h : ℝ} (hn : 1 ≤ n) (hB : 0 < B) (hK : 2 ≤ K)
    (hp : 0 ≤ p) (hp1 : p < 1) (hδ : 0 < δ) (hst : δ < 1/((B:ℝ)*(K:ℝ)))
    (hc : (p/(K:ℝ)) * (9*(M:ℝ)) ≤ (1-p)/2)
    (E : Set (CenteredCube.Space n)) (hE : MeasurableSet E)
    (hW : ∀ x ∈ E, ∃ L : ℝ, 0 < L ∧ L ≤ 2 ∧
      h < ∑ i, Real.log (1+actualWindowPerturbation f M p δ L (x i))) :
    ENNReal.ofReal (Real.exp h * (CenteredCube.sqrtCellLaw n).real E *
      (1-1/(n:ℝ)^2)^n) ≤ CenteredCube.weakConstant n := by
  apply CenteredCube.weakConstant_ge_periodic_log_event hn (actualWitnessDensity f M p δ)
    (fun x => (by linarith : 0 ≤ (1-p)/2).trans
      (actualWitnessDensity_positive_of_coarse f M hp hp1 hδ hc x))
    (actualWitnessDensity_intervalIntegrable f M p δ hδ)
    (actualWitnessDensity_periodic f M p δ) (actualWitnessDensity_unit_mass f M p δ hB hK hδ hst)
    h E hE
  intro x hx
  obtain ⟨L,hL,hL2,hb⟩ := hW x hx
  refine ⟨L,hL,hL2,actual_intervalSource_positive f M hp hp1 hδ hL hc,?_⟩
  unfold CenteredCube.periodicLogScore
  simp_rw [actual_intervalSource_eq_perturbation]
  exact hb

#print axioms weakConstant_ge_actual_witness_iid_event

#print axioms actualWitnessDensity_unit_mass
#print axioms actualWitnessDensity_periodic
#print axioms actualWitnessDensity_positive
end CenteredCubeSqrt
