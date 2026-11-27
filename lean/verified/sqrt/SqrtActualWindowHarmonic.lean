import SqrtWindowHarmonicFubini
import SqrtPaperAtomicFourier

namespace CenteredCubeSqrt
open MeasureTheory Set
open scoped Interval BigOperators
set_option maxHeartbeats 1400000

noncomputable def atomCosineMoment {B K : ℕ} [NeZero K] (f : ZMod K → Fin B) (m : ℕ) : ℝ :=
  ∑ j : ZMod K, Real.cos (2*Real.pi*(m:ℝ)*paperAtomCenter f j)

noncomputable def actualBoxSinc (δ : ℝ) (m : ℕ) :=
  Real.sin (Real.pi*(m:ℝ)*δ)/(Real.pi*(m:ℝ)*δ)

noncomputable def atomHarmonicCoefficient {B K : ℕ} [NeZero K] (f : ZMod K → Fin B)
    (δ : ℝ) (m : ℕ) :=
  actualBoxSinc δ m * (atomCosineMoment f m / (Real.pi*(m:ℝ)))

theorem single_box_window_continuous {δ : ℝ} (hδ : 0<δ) (a L : ℝ) :
    Continuous (fun x => ∫ y in x-L/2..x+L/2, periodicBoxDensity δ a y) := by
  let F (x : ℝ) := ∫ y in (0:ℝ)..x, periodicBoxDensity δ a y
  have hI := fun a' b' => periodicBoxDensity_intervalIntegrable δ a a' b' hδ
  have hc : Continuous F := intervalIntegral.continuous_primitive hI 0
  have E : (fun x : ℝ => ∫ y in x-L/2..x+L/2, periodicBoxDensity δ a y) =
    fun x => F (x+L/2)-F (x-L/2) := by
    funext x
    have h := intervalIntegral.integral_add_adjacent_intervals (hI 0 (x-L/2)) (hI (x-L/2) (x+L/2))
    dsimp [F]
    linarith
  rw [E]
  exact (hc.comp (continuous_id.add continuous_const)).sub (hc.comp (continuous_id.sub continuous_const))

theorem actual_atomic_window_harmonic {B K : ℕ} [NeZero K] (f : ZMod K → Fin B)
    {δ L : ℝ} (hδ0 : 0<δ) (hδ1 : δ<1) (hL : 0≤L) {m : ℕ} (hm : 0<m) :
    (∫ x in (0:ℝ)..1, actualAtomicWindow f δ L x*Real.cos (2*Real.pi*(m:ℝ)*x)) =
      atomHarmonicCoefficient f δ m * Real.sin (Real.pi*(m:ℝ)*L) := by
  let C (x : ℝ) := Real.cos (2*Real.pi*(m:ℝ)*x)
  let W (j : ZMod K) (x : ℝ) := ∫ y in x-L/2..x+L/2, periodicBoxDensity δ (paperAtomCenter f j) y
  have hc : Continuous C := by unfold C; fun_prop
  have hw (j : ZMod K) : Continuous (W j) := single_box_window_continuous hδ0 _ L
  have hσ : Continuous (fun x => ∑ j : ZMod K, W j x*C x) :=
    continuous_finsetSum _ (fun j _ => (hw j).mul hc)
  have e (x : ℝ) : actualAtomicWindow f δ L x*C x =
      (∑ j : ZMod K, W j x*C x)-((K:ℝ)*L)*C x := by
    unfold actualAtomicWindow
    rw [sub_mul,Finset.sum_mul]
  change (∫ x in (0:ℝ)..1, actualAtomicWindow f δ L x*C x) = _
  simp_rw [e]
  rw [intervalIntegral.integral_sub (hσ.intervalIntegrable _ _)
    ((hc.const_mul _).intervalIntegrable _ _),intervalIntegral.integral_const_mul]
  have c0 : (∫ x in (0:ℝ)..1,C x)=0 := by
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
    have h := integral_cos_n_period k
    convert h using 2; simp [C,Nat.cast_succ]; ring
  rw [c0,mul_zero,sub_zero,intervalIntegral.integral_finsetSum]
  · simp_rw [show (fun j : ZMod K => ∫ x in (0:ℝ)..1,W j x*C x) =
      fun j => (Real.sin (Real.pi*(m:ℝ)*L)/(Real.pi*(m:ℝ)))*actualBoxSinc δ m*
        Real.cos (2*Real.pi*(m:ℝ)*paperAtomCenter f j) by
      funext j
      exact actual_single_box_window_cosine hδ0 hδ1 hL hm]
    rw [←Finset.mul_sum]
    unfold atomHarmonicCoefficient atomCosineMoment
    ring
  · exact fun j _ => ((hw j).mul hc).intervalIntegrable _ _

theorem atomCosineMoment_re {B K : ℕ} [NeZero K] (f : ZMod K → Fin B) (m : ℕ) :
    atomCosineMoment f m=(actualFourierAtomSum f m).re := by
  unfold atomCosineMoment actualFourierAtomSum
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have e : 2*(Real.pi:ℂ)*Complex.I*(m:ℂ)*(paperAtomCenter f j:ℂ) =
      ((2*Real.pi*(m:ℝ)*paperAtomCenter f j:ℝ):ℂ)*Complex.I := by push_cast; ring
  rw [e,Complex.exp_ofReal_mul_I_re]

theorem actualBoxSinc_abs_le {δ : ℝ} (hδ : 0<δ) {m : ℕ} (hm : 0<m) :
    |actualBoxSinc δ m|≤1 := by
  unfold actualBoxSinc
  have hp : 0<Real.pi*(m:ℝ)*δ := by
    have h : 0<(m:ℝ):=by exact_mod_cast hm
    positivity
  rw [abs_div,abs_of_pos hp]
  exact (div_le_one hp).mpr ((Real.abs_sin_le_abs).trans_eq (abs_of_pos hp))

#print axioms actual_atomic_window_harmonic
#print axioms atomCosineMoment_re

end CenteredCubeSqrt
