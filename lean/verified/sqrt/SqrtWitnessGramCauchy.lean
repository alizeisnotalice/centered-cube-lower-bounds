import SqrtSafeWitnessGramDiagonal
namespace CenteredCubeSqrt
open MeasureTheory Set
open scoped Interval BigOperators
set_option maxHeartbeats 1000000

theorem periodInner_const_mul_left {F G : ℝ→ℝ} (c : ℝ) :
    periodInner (fun x => c*F x) G=c*periodInner F G := by
  unfold periodInner
  simp_rw [mul_assoc]
  rw [intervalIntegral.integral_const_mul]

theorem periodInner_const_mul_right {F G : ℝ→ℝ} (c : ℝ) :
    periodInner F (fun x => c*G x)=c*periodInner F G := by
  unfold periodInner
  simp_rw [show ∀ x, F x*(c*G x)=c*(F x*G x) by intro x; ring]
  rw [intervalIntegral.integral_const_mul]

theorem periodInner_cauchy_real {F G : ℝ→ℝ} (hF : Continuous F) (hG : Continuous G)
    (hF0 : 0<periodInner F F) :
    |periodInner F G| ≤ Real.sqrt (periodInner F F*periodInner G G) := by
  let A := periodInner F F
  let B := periodInner G G
  let C := periodInner F G
  let t := C/A
  let f (x : ℝ) := t*F x
  let g (x : ℝ) := -1*G x
  have fact : 0≤periodL2Sq (fun x => f x+g x) := periodL2Sq_nonnegative _
  have h0 : 0<A := hF0
  rw [periodL2Sq_add (hF.const_mul t) (hG.const_mul (-1))] at fact
  have hf : periodL2Sq f=t^2*A := by
    unfold f
    rw [periodL2Sq_mul_const,←periodInner_self_eq_L2Sq]
  have hg : periodL2Sq g=B := by
    unfold g
    rw [periodL2Sq_mul_const,←periodInner_self_eq_L2Sq]
    norm_num
    rfl
  have hi : periodInner f g= -(t*C) := by
    unfold f g
    rw [periodInner_const_mul_left,periodInner_const_mul_right]
    change t*(-1*C)=_
    ring
  rw [hf,hg,hi] at fact
  have e : t^2*A + 2* (-(t*C)) + B = (A*B-C^2)/A := by
    unfold t
    field_simp
    ring
  rw [e] at fact
  have hp : 0≤A*B-C^2 := (div_nonneg_iff.mp fact).resolve_right (fun h => (not_le_of_gt h0) h.2) |>.1
  change |C|≤Real.sqrt (A*B)
  apply Real.le_sqrt_of_sq_le
  rw [sq_abs]
  linarith

theorem periodInner_cauchy_both_continuous {F G : ℝ→ℝ} (hF : Continuous F) (hG : Continuous G) :
    |periodInner F G| ≤ Real.sqrt (periodInner F F*periodInner G G) := by
  let A := periodInner F F
  let B := periodInner G G
  let C := periodInner F G
  have hA : 0≤A := by unfold A; rw [periodInner_self_eq_L2Sq]; exact periodL2Sq_nonnegative _
  rcases lt_or_eq_of_le hA with h|h
  · exact periodInner_cauchy_real hF hG h
  · have H (t : ℝ) : 0≤2*t*C+B := by
      have hh := periodL2Sq_nonnegative (fun x => t*F x+G x)
      rw [periodL2Sq_add (hF.const_mul t) hG,periodL2Sq_mul_const,
        ←periodInner_self_eq_L2Sq,←periodInner_self_eq_L2Sq,
        periodInner_const_mul_left] at hh
      change 0≤t^2*A+2*(t*C)+B at hh
      rw [←h,mul_zero,zero_add] at hh
      linarith
    have hC : C=0 := by
      by_contra hn
      have h' := H ((-(B+1))/(2*C))
      have eq : 2*((-(B+1))/(2*C))*C+B= -1 := by field_simp; ring
      rw [eq] at h'
      norm_num at h'
    change |C|≤Real.sqrt (A*B)
    rw [hC,←h,zero_mul,Real.sqrt_zero,abs_zero]

theorem witnessGram_entry_cauchy {B K : ℕ} [NeZero K] (f : ZMod K→Fin B)
    (M : ℕ) {δ : ℝ} (hδ : 0<δ) (L J : ℝ) :
    |actualWitnessGram f M δ L J| ≤
      Real.sqrt (actualWitnessGram f M δ L L*actualWitnessGram f M δ J J) := by
  unfold actualWitnessGram
  exact periodInner_cauchy_both_continuous
    ((actualAtomicWindow_continuous f hδ L).add (actualLowSpectrum_continuous M L))
    ((actualAtomicWindow_continuous f hδ J).add (actualLowSpectrum_continuous M J))

#print axioms witnessGram_entry_cauchy
end CenteredCubeSqrt
