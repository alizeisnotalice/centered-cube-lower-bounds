import SqrtActualLocalVariance

namespace CenteredCubeSqrt
open MeasureTheory
open scoped Interval
set_option maxHeartbeats 1600000

theorem periodInner_add_right {f g h : ℝ → ℝ} (hf : Continuous f)
    (hg : Continuous g) (hh : Continuous h) :
    periodInner f (fun x => g x+h x)=periodInner f g+periodInner f h := by
  unfold periodInner
  simp_rw [mul_add]
  exact intervalIntegral.integral_add ((hf.mul hg).intervalIntegrable _ _)
    ((hf.mul hh).intervalIntegrable _ _)

theorem actual_baseline_increment_finite {B K : ℕ} [NeZero K]
    (f : ZMod K → Fin B) (M : ℕ) (hB : 0<B) (hk : 2≤K)
    {n p v eps T L0 s t : ℝ}
    (hn : 0≤n) (hscale : n*p^2=(29/9)*(K:ℝ)^2*v)
    (hv : 0<v) (he : 0<eps) (he4 : eps≤1/4) (hBv : (B:ℝ)≤2*v)
    (hT : 0≤T) (hm : (T+eps/2)/((K:ℝ)*v)<1/4)
    (hs : -T≤s) (hst : s≤t) (ht : t≤T) (h0 : 1≤L0)
    (hL_s : 1≤localLength L0 ((K:ℝ)*v) s)
    (hL_t : 1≤localLength L0 ((K:ℝ)*v) t) :
    let delta := eps/((K:ℝ)*v)
    let Ls := localLength L0 ((K:ℝ)*v) s
    let Lt := localLength L0 ((K:ℝ)*v) t
    |n*periodInner (actualWindowPerturbation f M p delta L0)
      (fun x => actualWindowPerturbation f M p delta Lt x-
        actualWindowPerturbation f M p delta Ls x)| ≤
      (29/9)*28*(t-s) +
      ((29/9)*49+(29/3)*(16*localSpecConst+392)*T^2)/(2*(K:ℝ)) := by
  let δ := eps/((K:ℝ)*v)
  let Ls := localLength L0 ((K:ℝ)*v) s
  let Lt := localLength L0 ((K:ℝ)*v) t
  let A := atomicWindowIncrement f eps v L0 s t
  let U := frozenAtomicPulse f p eps v L0 s t
  let W := actualWindowRemainder f M p eps v L0 s t
  let F := actualWindowPerturbation f M p δ L0
  let q := |p|/(K:ℝ)
  let Z := (K:ℝ)*v
  have hK : 0<(K:ℝ) := by exact_mod_cast (show 0<K by omega)
  have hL0 : 0<L0 := by linarith
  have hδ : 0<δ := by dsimp [δ]; positivity
  have hq : 0≤q := by dsimp [q]; positivity
  have hZ : 0<Z := mul_pos hK hv
  have hqscale : n*q^2=(29/9)*v := by
    dsimp [q]
    rw [div_pow, sq_abs, ←mul_div_assoc, hscale]
    field_simp
  have hu : Continuous U := continuous_const.mul (atomicWindowIncrement_continuous f he hv)
  have ha : Continuous A := atomicWindowIncrement_continuous f he hv
  have hw : Continuous W := actualWindowRemainder_continuous f M p he hv L0 s t
  have hδb := box_width_small_for_local_design (show 0<K by omega) hB hv he he4 hBv
  have hfEq : F = fun x => (p/((K:ℝ)*L0)) *
      (actualAtomicWindow f δ L0 x+actualLowSpectrum M L0 x) := by
    funext x
    exact actualWindowPerturbation_formula f M p hδ hL0 x
  have hf : Continuous F := by
    rw [hfEq]
    exact continuous_const.mul ((actualAtomicWindow_continuous f hδ _).add
      (actualLowSpectrum_continuous M _))
  have hcoef : |p/((K:ℝ)*L0)|≤q := by
    rw [abs_div, abs_of_pos (mul_pos hK hL0)]
    exact div_le_div_of_nonneg_left (abs_nonneg _) hK (le_mul_of_one_le_right hK.le h0)
  have hfb (x : ℝ) : |F x|≤7*q := by
    rw [hfEq,abs_mul]
    have e := actual_compensated_window_abs_le_seven f M hB hk (L:=L0) hδ hδb x
    have h := mul_le_mul hcoef e (abs_nonneg _) hq
    linarith
  have hlu : (∫ x in (0:ℝ)..1, |U x|) ≤ q*(4*(t-s)/v) := by
    have hA := actual_atomic_increment_L1 f (L0:=L0) he hv hT hm hs hst ht
    have e : (fun x => |U x|) = fun x => |p/((K:ℝ)*L0)| * |A x| := by
      funext x
      exact abs_mul _ _
    rw [e,intervalIntegral.integral_const_mul]
    have hnA : 0≤(∫ x in (0:ℝ)..1, |A x|) :=
      intervalIntegral.integral_nonneg_of_forall (by norm_num) (fun _ => abs_nonneg _)
    exact mul_le_mul hcoef hA hnA hq
  have hU : n*|periodInner F U|≤(29/9)*28*(t-s) := by
    have h := (abs_periodInner_uniform_L1 hf hu hfb).trans
      (mul_le_mul_of_nonneg_left hlu (show 0≤7*q by positivity))
    refine (mul_le_mul_of_nonneg_left h hn).trans ?_
    rw [show n*(7*q*(q*(4*(t-s)/v)))=n*q^2*(28*(t-s)/v) by ring, hqscale]
    field_simp; rfl
  have hF2 : n*periodL2Sq F≤(29/9)*49*v := by
    have h := mul_le_mul_of_nonneg_left
      (periodL2Sq_le_uniform hf (show 0≤7*q by positivity) hfb) hn
    calc
      _ ≤ n*(7*q)^2 := h
      _ = _ := by rw [show n*(7*q)^2=49*(n*q^2) by ring,hqscale]; ring
  let C := (29/3)*((16*localSpecConst+392)*T^2)
  have hW2 : n*periodL2Sq W≤C/((K:ℝ)^2*v) := by
    exact actualWindowRemainder_L2_bound f M hB hk hn hscale he he4 hv hBv
      h0 hL_s hL_t hT (abs_le.mpr ⟨hs, hst.trans ht⟩) (abs_le.mpr ⟨hs.trans hst,ht⟩)
  have hW : n*|periodInner F W|≤((29/9)*49+C)/(2*(K:ℝ)) := by
    have e := abs_periodInner_young hf hw (z:=1/Z) (by positivity)
    rw [show 1/(1/Z)=Z by simp] at e
    refine (mul_le_mul_of_nonneg_left e hn).trans ?_
    rw [show n*((1/Z*periodL2Sq F+Z*periodL2Sq W)/2) =
      ((1/Z)*(n*periodL2Sq F)+Z*(n*periodL2Sq W))/2 by ring]
    have eF := mul_le_mul_of_nonneg_left hF2 (show 0≤1/Z by positivity)
    have eW := mul_le_mul_of_nonneg_left hW2 hZ.le
    calc
      _ ≤ (1/Z*((29/9)*49*v)+Z*(C/((K:ℝ)^2*v)))/2 := by linarith
      _ = _ := by dsimp [Z]; field_simp
  have hfull : (fun x => actualWindowPerturbation f M p δ Lt x-
      actualWindowPerturbation f M p δ Ls x) = fun x => U x+W x := by
    funext x
    exact actualWindowIncrement_atomic_remainder f M p he hv hL0
      (by linarith [hL_s]) (by linarith [hL_t]) x
  change |n*periodInner F (fun x => actualWindowPerturbation f M p δ Lt x-
    actualWindowPerturbation f M p δ Ls x)| ≤ _
  rw [hfull,periodInner_add_right hf hu hw,abs_mul,abs_of_nonneg hn]
  exact (mul_le_mul_of_nonneg_left (abs_add_le _ _) hn).trans (by
    rw [mul_add]
    simpa only [C,mul_assoc] using add_le_add hU hW)

#print axioms actual_baseline_increment_finite

end CenteredCubeSqrt
