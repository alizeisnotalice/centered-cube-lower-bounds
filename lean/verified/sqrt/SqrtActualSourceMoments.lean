import SqrtActualPacketLocal
import SqrtActualLocalPolarization

namespace CenteredCubeSqrt
open Set Filter MeasureTheory
open scoped Topology BigOperators
set_option maxHeartbeats 1350000
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem actual_perturbation_inner_exact {B K : ℕ} [NeZero K] (f : ZMod K→Fin B)
    (M : ℕ) (p : ℝ) {δ L J : ℝ} (hδ : 0<δ) (hL : 0<L) (hJ : 0<J) :
    periodInner (actualWindowPerturbation f M p δ L) (actualWindowPerturbation f M p δ J) =
      (p/((K:ℝ)*L))*(p/((K:ℝ)*J))*actualWitnessGram f M δ L J := by
  have E (A : ℝ) (ha : 0<A) : actualWindowPerturbation f M p δ A=
      (fun x => (p/((K:ℝ)*A))*(actualAtomicWindow f δ A x+actualLowSpectrum M A x)) :=
    funext (actualWindowPerturbation_formula f M p hδ ha)
  rw [E L hL,E J hJ,periodInner_const_mul_left,periodInner_const_mul_right]
  unfold actualWitnessGram
  ring

theorem actual_safe_q_relative_bound {b d : ℕ} [NeZero (2^d-1)]
    (hd : 0<d) (g : (LabelField d)ˣ) (hg : orderOf g=2^d-1) (t : Fin b→LabelField d)
    (w p : ℝ) (n : ℕ) {L : ℝ} (hL : L∈paperScaleWindow)
    (hM : PaperMeshParameters w (paperV p n d) b d)
    (hcert : ActualPaperKernelConclusions hd g hg t w (paperV p n d) L L) :
    let v := paperV p n d
    let K := (paperPeriod d:ℝ)
    let B := (2:ℝ)^b
    let M := paperMeshM v
    let δ := paperMeshDelta w K v
    let E := paperAtomicCrossSmoothing w K B v M
    let X := actualWindowPerturbation (ordinalPhaseLabel hd g hg t) M p δ L
    |(n:ℝ)*periodL2Sq X-v|≤v*paperKernelRelError B K E M := by
  let v := paperV p n d
  let K := (paperPeriod d:ℝ)
  let B := (2:ℝ)^b
  let M := paperMeshM v
  let δ := paperMeshDelta w K v
  let E := paperAtomicCrossSmoothing w K B v M
  let f := ordinalPhaseLabel hd g hg t
  let X := actualWindowPerturbation f M p δ L
  let G := actualWitnessGram f M δ L L
  have hK : 0<K := by dsimp [K]; exact_mod_cast (show 0<paperPeriod d by have := hM.period_lower; omega)
  have hL' : 0<L := by linarith [hL.1]
  have vpos : 0<v := by linarith [hM.v_ge_four]
  have hs : (n:ℝ)*p^2=(29/9)*K^2*v := actual_v_exact_scale p hd
  have H := actual_perturbation_inner_exact f M p hM.delta_positive hL' hL'
  rw [periodInner_self_eq_L2Sq] at H
  change periodL2Sq X=(p/(K*L))*(p/(K*L))*G at H
  have q : (n:ℝ)*periodL2Sq X=v*(G/((27/29)*L^2/3)) := by
    rw [H]
    have A : (n:ℝ)*(p/(K*L)*(p/(K*L))*G)=((n:ℝ)*p^2)*G/(K*L)^2 := by ring
    rw [A,hs]
    field_simp [hK.ne',hL'.ne']
    ring
  have hErr : |G/((27/29)*L^2/3)-1|≤paperKernelRelError B K E M :=
    hcert.1.2
  change |(n:ℝ)*periodL2Sq X-v|≤_
  rw [q,show v*(G/(27/29*L^2/3))-v=v*(G/(27/29*L^2/3)-1) by ring,
    abs_mul,abs_of_pos vpos]
  exact mul_le_mul_of_nonneg_left hErr vpos.le

theorem actual_source_uniform_amplitude {B K : ℕ} [NeZero K]
    (f : ZMod K→Fin B) (M : ℕ) (hB : 0<B) (hk : 2≤K) {p δ L : ℝ}
    (hδ : 0<δ) (hδB : δ<1/((B:ℝ)*K)) (hL : 1≤L) (x : ℝ) :
    |actualWindowPerturbation f M p δ L x|≤7*|p|/(K:ℝ) := by
  have hK : 0<(K:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne K)
  have hL0 : 0<L := by linarith
  rw [actualWindowPerturbation_formula f M p hδ hL0,abs_mul,abs_div,
    abs_of_pos (mul_pos hK hL0)]
  have h := actual_compensated_window_abs_le_seven f M hB hk hδ hδB (L:=L) x
  refine (mul_le_mul_of_nonneg_left h (by positivity)).trans ?_
  have Q : |p|/((K:ℝ)*L)≤|p|/(K:ℝ) :=
    div_le_div_of_nonneg_left (abs_nonneg _) hK (by nlinarith [mul_le_mul_of_nonneg_left hL hK.le])
  calc
    |p|/((K:ℝ)*L)*7 ≤ |p|/(K:ℝ)*7 := mul_le_mul_of_nonneg_right Q (by norm_num)
    _ = _ := by ring

theorem actual_amp_scaled_tendsto {p : ℝ} (hp : 0<p) (d : ℕ→ℕ)
    (h : ∀ᶠ n : ℕ in atTop, 0<d n ∧
      16*Real.log n≤paperV p n (d n) ∧ paperV p n (d n)<144*Real.log n) :
    Tendsto (fun n : ℕ => (7*|p|/(paperPeriod (d n):ℝ))*paperV p n (d n)) atTop (𝓝 0) := by
  have K := paper_period_growth_of_choice hp d h 1
  have H := (tendsto_inv_atTop_zero.comp K).const_mul (7*|p|)
  rw [mul_zero] at H
  refine H.congr ?_
  intro n
  simp only [Function.comp_def,pow_one,inv_div]
  ring

theorem actual_v_sq_over_n_tendsto {p : ℝ} (d : ℕ→ℕ)
    (h : ∀ᶠ n : ℕ in atTop, 0<d n ∧
      16*Real.log n≤paperV p n (d n) ∧ paperV p n (d n)<144*Real.log n) :
    Tendsto (fun n : ℕ => (paperV p n (d n))^2/(n:ℝ)) atTop (𝓝 0) := by
  have H := (log_power_div_nat_tendsto 2).const_mul (144^2:ℝ)
  rw [mul_zero] at H
  have hv := paper_v_tendsto (h.mono fun _ H => H.2.1)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds H
    (Eventually.of_forall (fun _ => by positivity)) ?_
  filter_upwards [h,hv.eventually_ge_atTop 0] with n hn hvn
  have P := pow_le_pow_left₀ hvn hn.2.2.le 2
  rw [mul_pow] at P
  calc
    _ ≤ (144^2*(Real.log n)^2)/(n:ℝ) := div_le_div_of_nonneg_right P (by positivity)
    _ = _ := by ring

theorem actual_perturbation_normalized_eq {B K : ℕ} [NeZero K] (f : ZMod K→Fin B)
    (M : ℕ) {p δ L J : ℝ} (hp : 0<p) (hδ : 0<δ) (hL : 0<L) (hJ : 0<J) :
    periodInner (actualWindowPerturbation f M p δ L) (actualWindowPerturbation f M p δ J)/
      Real.sqrt (periodL2Sq (actualWindowPerturbation f M p δ L)*
        periodL2Sq (actualWindowPerturbation f M p δ J)) =
      actualNormalizedGram f M δ L J := by
  rw [←periodInner_self_eq_L2Sq,←periodInner_self_eq_L2Sq,
    actual_perturbation_inner_exact f M p hδ hL hJ,actual_perturbation_inner_exact f M p hδ hL hL,
    actual_perturbation_inner_exact f M p hδ hJ hJ]
  let a := p/((K:ℝ)*L)
  let b := p/((K:ℝ)*J)
  let A := actualWitnessGram f M δ L L
  let B := actualWitnessGram f M δ J J
  let C := actualWitnessGram f M δ L J
  have hK : 0<(K:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne K)
  have ab : 0<a*b := by unfold a b; positivity
  change (a*b*C)/Real.sqrt ((a*a*A)*(b*b*B))=C/Real.sqrt (A*B)
  rw [show (a*a*A)*(b*b*B)=(a*b)^2*(A*B) by ring,
    Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq ab.le]
  exact mul_div_mul_left C _ ab.ne'

#print axioms actual_perturbation_normalized_eq
#print axioms actual_perturbation_inner_exact
#print axioms actual_safe_q_relative_bound
#print axioms actual_source_uniform_amplitude
#print axioms actual_amp_scaled_tendsto
#print axioms actual_v_sq_over_n_tendsto
end CenteredCubeSqrt
