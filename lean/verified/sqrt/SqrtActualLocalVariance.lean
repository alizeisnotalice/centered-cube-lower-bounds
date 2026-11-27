import SqrtWindowRemainderL2
import SqrtPeriodL2Error
import SqrtAtomicWindowL1

namespace CenteredCubeSqrt

open MeasureTheory
open scoped BigOperators Interval
open Classical

set_option maxHeartbeats 2500000
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

noncomputable def frozenAtomicPulse {B K : ℕ} [NeZero K] (f : ZMod K → Fin B)
    (p eps v L0 s t x : ℝ) : ℝ :=
  (p/((K:ℝ)*L0))*atomicWindowIncrement f eps v L0 s t x

theorem scaled_frozen_atomic_variance {B K : ℕ} [NeZero K] (f : ZMod K → Fin B)
    {n p eps v L0 s t : ℝ} (hL0 : 0<L0)
    (hscale : n*p^2=(29/9)*(K:ℝ)^2*v) :
    n*periodL2Sq (frozenAtomicPulse f p eps v L0 s t) =
      (29/(9*L0^2))*(v*periodL2Sq (atomicWindowIncrement f eps v L0 s t)) := by
  unfold frozenAtomicPulse
  rw [periodL2Sq_mul_const,← mul_assoc,div_pow,← mul_div_assoc,hscale]
  have hK : (K:ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne K)
  field_simp

/-- Quantitative actual local squared-distance law (untilted), with explicit
uniform remainder; its main coefficient is 58/(9L0²). The input safety
condition is on the actual coarse integer lifts, not random labels. -/
theorem actual_local_variance_finite {b d : ℕ} [NeZero (2^d-1)]
    [NeZero (2^b*(2^d-1))] (hd : 0<d) (g : (LabelField d)ˣ)
    (hg : orderOf g=2^d-1) {tβ : Fin b → LabelField d}
    (htβ : LinearIndependent (ZMod 2) tβ) (hdim : 2*b≤d)
    (hk : 2≤(2^d-1:ℕ))
    (h1 : (phaseState hd g hg 1 : LabelField d) ≠ 1)
    (h1' : (phaseState hd g hg 1 : LabelField d) ∉ labelRatioSet tβ)
    (M : ℕ) {n p v eps T L0 s t : ℝ} {D : ℕ}
    (hn : 0≤n) (hscale : n*p^2=(29/9)*(((2^d-1:ℕ):ℝ))^2*v)
    (hv : 0<v) (he : 0<eps) (he4 : eps≤1/4) (hT : 0≤T)
    (hV : 2*T+eps<v) (hBv : ((2^b:ℕ):ℝ)≤2*v)
    (hD : 2*(2*T+eps)+1≤D)
    (hm : (T+eps/2)/((((2^d-1:ℕ):ℝ))*v)<1/4)
    (hs : -T≤s) (hst : s≤t) (ht : t≤T)
    (h0 : 1≤L0)
    (hL_s : 1≤localLength L0 ((((2^d-1:ℕ):ℝ))*v) s)
    (hL_t : 1≤localLength L0 ((((2^d-1:ℕ):ℝ))*v) t)
    (hSafe : ∀ k : ℤ, |(k:ℝ)-(((2^d-1:ℕ):ℝ))*L0|<2 →
      (phaseState hd g hg (k:ZMod (2^d-1)) : LabelField d) ≠ 1 ∧
      (phaseState hd g hg (k:ZMod (2^d-1)) : LabelField d) ∉ labelRatioSet tβ) :
    let f := ordinalPhaseLabel hd g hg tβ
    let B := ((2^b:ℕ):ℝ)
    let K := ((2^d-1:ℕ):ℝ)
    let delta := eps/(K*v)
    let Ls := localLength L0 (K*v) s
    let Lt := localLength L0 (K*v) t
    let P := 2*((2*(D:ℝ)+1)*(4*(2*T+eps)/B^2)*(2*T)) +
      2*((2*(D:ℝ)+1)*(2/B)*(2*T)) + 4*(t-s)^2/v
    let R := (29/3)*((16*localSpecConst+392)*T^2)/(K^2*v)
    |n*periodL2Sq (fun x => actualWindowPerturbation f M p delta Lt x -
      actualWindowPerturbation f M p delta Ls x) -
      (58/(9*L0^2))*pulseOverlap eps s t s t 0| ≤
      (29/9)*P+(1/K)*((29/9)*(4*T+P))+(1+K)*R := by
  let f := ordinalPhaseLabel hd g hg tβ
  let B : ℝ := ((2^b:ℕ):ℝ)
  let K : ℝ := ((2^d-1:ℕ):ℝ)
  let δ := eps/(K*v)
  let Ls := localLength L0 (K*v) s
  let Lt := localLength L0 (K*v) t
  let P := 2*((2*(D:ℝ)+1)*(4*(2*T+eps)/B^2)*(2*T)) +
    2*((2*(D:ℝ)+1)*(2/B)*(2*T)) + 4*(t-s)^2/v
  let R := (29/3)*((16*localSpecConst+392)*T^2)/(K^2*v)
  let A := atomicWindowIncrement f eps v L0 s t
  let U := frozenAtomicPulse f p eps v L0 s t
  let W := actualWindowRemainder f M p eps v L0 s t
  let O := pulseOverlap eps s t s t 0
  have hK : 0<K := by
    dsimp [K]
    exact_mod_cast (show 0<(2^d-1:ℕ) by omega)
  have hL0 : 0<L0 := by linarith
  have huc : Continuous U := continuous_const.mul (atomicWindowIncrement_continuous f he hv)
  have hwc : Continuous W := actualWindowRemainder_continuous f M p he hv L0 s t
  have hA := actual_local_atomic_covariance (s:=s) (t:=t) (s':=s) (t':=t)
    hd g hg htβ hdim h1 h1' hv he hT hV hBv hD hm hs hst ht hs hst ht hSafe
  have PA : |v*periodL2Sq A-2*O|≤P := by
    dsimp only at hA
    simpa only [A,O,P,B,periodL2Sq,pow_two,mul_assoc] using hA
  have hP : 0≤P := (abs_nonneg _).trans PA
  have hUeq : n*periodL2Sq U=(29/(9*L0^2))*(v*periodL2Sq A) :=
    scaled_frozen_atomic_variance f hL0 hscale
  have hcoef : (29:ℝ)/(9*L0^2)≤29/9 := by
    have hsq : (1:ℝ) ≤ L0^2 := by nlinarith
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    linarith
  have hUm : |n*periodL2Sq U-(58/(9*L0^2))*O|≤(29/9)*P := by
    rw [hUeq,show (29/(9*L0^2))*(v*periodL2Sq A)-(58/(9*L0^2))*O =
      (29/(9*L0^2))*(v*periodL2Sq A-2*O) by ring,abs_mul,
      abs_of_nonneg (by positivity : 0≤(29:ℝ)/(9*L0^2))]
    exact mul_le_mul hcoef PA (abs_nonneg _) (by norm_num)
  have hU2 : n*periodL2Sq U≤(29/9)*(4*T+P) := by
    have hO : O≤2*T := (pulseOverlap_bounded he hst).2.trans (by linarith)
    have hAx := (abs_le.mp PA).2
    rw [hUeq]
    calc
      _ ≤ (29/9)*(v*periodL2Sq A) :=
        mul_le_mul_of_nonneg_right hcoef (mul_nonneg hv.le (periodL2Sq_nonnegative _))
      _ ≤ _ := by linarith
  have hW : n*periodL2Sq W≤R := by
    apply actualWindowRemainder_L2_bound f M (by positivity) hk hn hscale he he4 hv hBv h0
      hL_s hL_t hT
    · exact abs_le.mpr ⟨hs, hst.trans ht⟩
    · exact abs_le.mpr ⟨hs.trans hst, ht⟩
  have hFull : (fun x => actualWindowPerturbation f M p δ Lt x-
      actualWindowPerturbation f M p δ Ls x) = fun x => U x+W x := by
    funext x
    exact actualWindowIncrement_atomic_remainder f M p he hv hL0
      (by linarith [hL_s]) (by linarith [hL_t]) x
  have herr := periodL2Sq_add_error huc hwc (z:=1/K) (by positivity)
  have hh : |n*periodL2Sq (fun x => U x+W x)-n*periodL2Sq U| ≤
      (1/K)*((29/9)*(4*T+P))+(1+K)*R := by
    rw [← mul_sub, abs_mul,abs_of_nonneg hn]
    have e : 1/(1/K)=K := by simp
    rw [e] at herr
    refine (mul_le_mul_of_nonneg_left herr hn).trans ?_
    rw [mul_add]
    have a := mul_le_mul_of_nonneg_left hU2 (show 0≤1/K by positivity)
    have c := mul_le_mul_of_nonneg_left hW (show 0≤1+K by positivity)
    nlinarith
  change |n*periodL2Sq (fun x => actualWindowPerturbation f M p δ Lt x-
    actualWindowPerturbation f M p δ Ls x)-(58/(9*L0^2))*O| ≤
      (29/9)*P+(1/K)*((29/9)*(4*T+P))+(1+K)*R
  rw [hFull]
  exact (abs_sub_le _ (n*periodL2Sq U) _).trans (by linarith)

#print axioms actual_local_variance_finite

end CenteredCubeSqrt
