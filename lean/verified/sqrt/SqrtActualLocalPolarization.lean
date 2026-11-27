import SqrtActualLocalAsymptotic
import SqrtWitnessGramCauchy
import SqrtActualBaselineIncrement

namespace CenteredCubeSqrt
open Set Filter MeasureTheory
open scoped Topology BigOperators
set_option maxHeartbeats 1500000

theorem periodL2Sq_sub_from_add {F G : ℝ→ℝ} (hF : Continuous F) (hG : Continuous G) :
    periodL2Sq (fun x => F x-G x)=periodL2Sq F-2*periodInner F G+periodL2Sq G := by
  simp_rw [sub_eq_add_neg]
  have H := periodL2Sq_add hF hG.neg
  have eq1 : periodL2Sq (fun x => -G x)=periodL2Sq G := by unfold periodL2Sq; simp_rw [neg_sq]
  have eq2 : periodInner F (fun x => -G x)= -(periodInner F G) := by
    have E := periodInner_const_mul_right (F:=F) (G:=G) (-1)
    simpa only [neg_one_mul] using E
  change periodL2Sq (fun x => F x+-G x)=periodL2Sq F+2*periodInner F (fun x => -G x)+
    periodL2Sq (fun x => -G x) at H
  change periodL2Sq (fun x => F x+-G x)=_
  rw [H,eq1,eq2]
  ring

theorem periodInner_anchored_polarization {F G H : ℝ→ℝ}
    (hF : Continuous F) (hG : Continuous G) (hH : Continuous H) :
    periodInner (fun x => F x-H x) (fun x => G x-H x) =
      (periodL2Sq (fun x => F x-H x)+periodL2Sq (fun x => G x-H x)-
        periodL2Sq (fun x => F x-G x))/2 := by
  let U (x : ℝ) := F x-H x
  let V (x : ℝ) := G x-H x
  have E : (fun x => U x-V x)=(fun x => F x-G x) := by funext x; unfold U V; ring
  have h := periodL2Sq_sub_from_add (show Continuous U from hF.sub hH) (show Continuous V from hG.sub hH)
  rw [E] at h
  change periodInner U V=(periodL2Sq U+periodL2Sq V-periodL2Sq (fun x => F x-G x))/2
  linarith

theorem scaled_anchoredGram_tendsto {l : Filter ℕ} {F G H : ℕ→ℝ→ℝ} {a b c : ℝ}
    (hC : ∀ᶠ n in l, Continuous (F n) ∧ Continuous (G n) ∧ Continuous (H n))
    (ha : Tendsto (fun n : ℕ => (n:ℝ)*periodL2Sq (fun x => F n x-H n x)) l (𝓝 a))
    (hb : Tendsto (fun n : ℕ => (n:ℝ)*periodL2Sq (fun x => G n x-H n x)) l (𝓝 b))
    (hc : Tendsto (fun n : ℕ => (n:ℝ)*periodL2Sq (fun x => F n x-G n x)) l (𝓝 c)) :
    Tendsto (fun n : ℕ => (n:ℝ)*periodInner (fun x => F n x-H n x) (fun x => G n x-H n x))
      l (𝓝 ((a+b-c)/2)) := by
  refine (((ha.add hb).sub hc).div_const 2).congr' ?_
  filter_upwards [hC] with n h
  rw [periodInner_anchored_polarization h.1 h.2.1 h.2.2]
  ring

theorem scaled_periodInner_cauchy {F G : ℝ→ℝ} (hF : Continuous F) (hG : Continuous G)
    {n A B : ℝ} (hn : 0≤n) (hA : n*periodL2Sq F≤A) (hB : n*periodL2Sq G≤B) :
    |n*periodInner F G|≤Real.sqrt (A*B) := by
  have hf : 0≤n*periodL2Sq F := mul_nonneg hn (periodL2Sq_nonnegative _)
  have hg : 0≤n*periodL2Sq G := mul_nonneg hn (periodL2Sq_nonnegative _)
  have H := periodInner_cauchy_both_continuous hF hG
  rw [periodInner_self_eq_L2Sq,periodInner_self_eq_L2Sq] at H
  rw [abs_mul,abs_of_nonneg hn]
  calc
    _ ≤ n*Real.sqrt (periodL2Sq F*periodL2Sq G) := mul_le_mul_of_nonneg_left H hn
    _ = Real.sqrt ((n*periodL2Sq F)*(n*periodL2Sq G)) := by
      rw [show n*periodL2Sq F*(n*periodL2Sq G)=n^2*(periodL2Sq F*periodL2Sq G) by ring,
        Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq hn]
    _ ≤ _ := Real.sqrt_le_sqrt (mul_le_mul hA hB hg (hf.trans hA))

theorem actualWindowPerturbation_continuous_length_fixed {B K : ℕ} [NeZero K] (f : ZMod K→Fin B)
    (M : ℕ) (p : ℝ) {δ L : ℝ} (hδ : 0<δ) (hL : 0<L) :
    Continuous (actualWindowPerturbation f M p δ L) := by
  have F := actualWindowPerturbation_formula f M p hδ hL
  have e : actualWindowPerturbation f M p δ L=(fun x =>
      p/((K:ℝ)*L)*(actualAtomicWindow f δ L x+actualLowSpectrum M L x)) := by
    funext x
    exact F x
  rw [e]
  exact continuous_const.mul ((actualAtomicWindow_continuous f hδ L).add (actualLowSpectrum_continuous M L))

#print axioms scaled_anchoredGram_tendsto
#print axioms scaled_periodInner_cauchy
#print axioms actualWindowPerturbation_continuous_length_fixed
end CenteredCubeSqrt
