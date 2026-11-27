import SqrtWindowUniformBounds
import SqrtPeriodL2

namespace CenteredCubeSqrt

open MeasureTheory
open scoped BigOperators Interval

set_option maxHeartbeats 2000000

noncomputable def localSpecConst : ℝ := (400/81)*Real.pi^2

theorem actualWindowRemainder_continuous {B K : ℕ} [NeZero K] (f : ZMod K → Fin B)
    (M : ℕ) (p : ℝ) {eps v : ℝ} (he : 0<eps) (hv : 0<v) (L0 s t : ℝ) :
    Continuous (actualWindowRemainder f M p eps v L0 s t) := by
  have hK : 0 < (K:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne K)
  have hd : 0<eps/((K:ℝ)*v) := by positivity
  have A (r : ℝ) := actualAtomicWindow_continuous f hd (localLength L0 ((K:ℝ)*v) r)
  have B0 (r : ℝ) := actualLowSpectrum_continuous M (localLength L0 ((K:ℝ)*v) r)
  unfold actualWindowRemainder
  dsimp
  exact continuous_const.mul (((((B0 t).sub (B0 s)).div_const _).add
    (continuous_const.mul ((A t).add (B0 t)))).sub
      (continuous_const.mul ((A s).add (B0 s))))

/-- Explicit O_T((K²v)⁻¹) bound on the frozen-denominator
error of the actual full density. No orthogonality is assumed. -/
theorem actualWindowRemainder_L2_bound {B K : ℕ} [NeZero K]
    (f : ZMod K → Fin B) (M : ℕ) (hB : 0<B) (hK : 2≤K)
    {n p eps v L0 T s t : ℝ}
    (hn : 0≤n) (hpv : n*p^2 = (29/9)*(K:ℝ)^2*v)
    (he : 0<eps) (he4 : eps≤1/4) (hv : 0<v) (hBv : (B:ℝ)≤2*v)
    (h0 : 1≤L0) (hL_s : 1≤localLength L0 ((K:ℝ)*v) s)
    (hL_t : 1≤localLength L0 ((K:ℝ)*v) t)
    (_hT : 0≤T) (hs : |s|≤T) (ht : |t|≤T) :
    n*periodL2Sq (actualWindowRemainder f M p eps v L0 s t) ≤
      (29/3)*((16*localSpecConst+392)*T^2)/((K:ℝ)^2*v) := by
  let C := (K:ℝ)*v
  let δ := eps/C
  let Ls := localLength L0 C s
  let Lt := localLength L0 C t
  let Hs := actualAtomicWindow f δ Ls
  let Ht := actualAtomicWindow f δ Lt
  let Bs := actualLowSpectrum M Ls
  let Bt := actualLowSpectrum M Lt
  let q (x : ℝ) := (Bt x-Bs x)/L0
  let a (x : ℝ) := (1/Lt-1/L0)*(Ht x+Bt x)
  let c (x : ℝ) := -(1/Ls-1/L0)*(Hs x+Bs x)
  have hKp : 0 < (K:ℝ) := by exact_mod_cast (show 0<K by omega)
  have hCp : 0 < C := mul_pos hKp hv
  have hδ0 : 0 < δ := div_pos he hCp
  have hδ : δ < 1/((B:ℝ)*K) := box_width_small_for_local_design (by omega) hB hv he he4 hBv
  have hL0 : 0<L0 := by linarith
  have q_cont : Continuous q :=
    ((actualLowSpectrum_continuous M Lt).sub (actualLowSpectrum_continuous M Ls)).div_const _
  have a_cont : Continuous a := continuous_const.mul
    ((actualAtomicWindow_continuous f hδ0 Lt).add (actualLowSpectrum_continuous M Lt))
  have c_cont : Continuous c := continuous_const.mul
    ((actualAtomicWindow_continuous f hδ0 Ls).add (actualLowSpectrum_continuous M Ls))
  have hq : periodL2Sq q ≤ localSpecConst*(4*T/C)^2 := by
    have hc : 0 ≤ localSpecConst := by unfold localSpecConst; positivity
    have hBdiff := actualLowSpectrum_difference_L2 M Lt Ls
    change periodL2Sq (fun x => Bt x-Bs x) ≤ localSpecConst*(Lt-Ls)^2 at hBdiff
    have e0 : q = (fun x => (1/L0)*(Bt x-Bs x)) := by
      funext x
      unfold q
      ring
    rw [e0,periodL2Sq_mul_const]
    have hcoef : (1/L0)^2 ≤ 1 := by
      have h1 : (1:ℝ)/L0 ≤ 1 := (div_le_one hL0).2 h0
      simpa using pow_le_pow_left₀ (by positivity) h1 2
    have hLdiff : |Lt-Ls| ≤ 4*T/C := by
      have es : Lt-Ls = 2*(t-s)/C := by dsimp [Lt,Ls,localLength]; ring
      rw [es,abs_div,abs_of_pos hCp,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤2)]
      apply div_le_div_of_nonneg_right _ hCp.le
      have hab := (abs_sub _ _).trans (add_le_add ht hs)
      linarith
    have hc2 : (Lt-Ls)^2 ≤ (4*T/C)^2 := by
      have he2 := pow_le_pow_left₀ (abs_nonneg _) hLdiff 2
      simpa [sq_abs] using he2
    calc
      _ ≤ 1*periodL2Sq (fun x => Bt x-Bs x) :=
        mul_le_mul_of_nonneg_right hcoef (periodL2Sq_nonnegative _)
      _ ≤ localSpecConst*(Lt-Ls)^2 := by simpa using hBdiff
      _ ≤ _ := mul_le_mul_of_nonneg_left hc2 hc
  have each {u : ℝ} (hu : |u|≤T) (huL : 1≤localLength L0 C u) :
      periodL2Sq (fun x => (1/localLength L0 C u-1/L0)*
        (actualAtomicWindow f δ (localLength L0 C u) x+actualLowSpectrum M (localLength L0 C u) x)) ≤
        (2*T/C)^2*49 := by
    rw [periodL2Sq_mul_const]
    have su : Continuous (fun x => actualAtomicWindow f δ (localLength L0 C u) x+
        actualLowSpectrum M (localLength L0 C u) x) :=
      (actualAtomicWindow_continuous f hδ0 _).add (actualLowSpectrum_continuous M _)
    have hvv := periodL2Sq_le_uniform su (by norm_num : (0:ℝ)≤7)
      (actual_compensated_window_abs_le_seven f M hB hK hδ0 hδ)
    have hc := (localLength_inverse_difference_bound hCp h0 huL).trans
      (div_le_div_of_nonneg_right (show 2*|u| ≤ 2*T by linarith) hCp.le)
    have h2 : (1/localLength L0 C u-1/L0)^2 ≤ (2*T/C)^2 := by
      simpa [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hc 2
    apply mul_le_mul h2 (by norm_num at hvv; exact hvv) (periodL2Sq_nonnegative _) (by positivity)
  have ha : periodL2Sq a ≤ (2*T/C)^2*49 := each ht hL_t
  have hc : periodL2Sq c ≤ (2*T/C)^2*49 := by
    have hh := each hs hL_s
    rw [periodL2Sq_mul_const] at hh
    unfold c
    rw [periodL2Sq_mul_const,neg_sq]
    exact hh
  have hthree := periodL2Sq_three_sum q_cont a_cont c_cont
  have hcomb : periodL2Sq (fun x => q x+a x+c x) ≤
      3*((16*localSpecConst+392)*T^2/C^2) := by
    have e : 3*(localSpecConst*(4*T/C)^2+(2*T/C)^2*49+(2*T/C)^2*49) =
        3*((16*localSpecConst+392)*T^2/C^2) := by ring
    linarith
  have e : actualWindowRemainder f M p eps v L0 s t =
      fun x => (p/(K:ℝ))*(q x+a x+c x) := by
    funext x
    unfold actualWindowRemainder q a c
    dsimp [Bt,Bs,Ht,Hs,Lt,Ls,δ,C]
    ring
  rw [e,periodL2Sq_mul_const,← mul_assoc]
  calc
    _ ≤ (n*(p/(K:ℝ))^2)*(3*((16*localSpecConst+392)*T^2/C^2)) :=
      mul_le_mul_of_nonneg_left hcomb (by positivity)
    _ = _ := by
      have e0 : n*(p/(K:ℝ))^2=(29/9)*v := by
        rw [div_pow,← mul_div_assoc,hpv]
        field_simp
      rw [e0]
      dsimp [C]
      field_simp
      ring

#print axioms actualWindowRemainder_continuous
#print axioms actualWindowRemainder_L2_bound

end CenteredCubeSqrt
