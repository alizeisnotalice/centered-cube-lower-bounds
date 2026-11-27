import SqrtPaperBudgetEligibility

namespace CenteredCubeSqrt
open Filter Set MvPolynomial
open scoped Topology BigOperators
set_option maxHeartbeats 2500000
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

noncomputable def paperScaleWindow : Set ℝ := Icc (10/9) (11/9)

def ActualPaperKernelConclusions {b d : ℕ} [NeZero (2^d-1)] (hd : 0<d) (g : (LabelField d)ˣ)
    (hg : orderOf g=2^d-1) (t : Fin b→LabelField d) (w v : ℝ) (L J : ℝ) : Prop :=
  let K := (paperPeriod d:ℝ)
  let B := (2:ℝ)^b
  let M := paperMeshM v
  let δ := paperMeshDelta w K v
  let f := ordinalPhaseLabel hd g hg t
  let E := paperAtomicCrossSmoothing w K B v M
  let EN := paperNearBudget B K E
  let V := paperKernelFloor B K E M
  let R := paperKernelRelError B K E M
  let τ := K * |J-L|/2
  let κ := actualNormalizedGram f M δ L J
  ((V≤actualWitnessGram f M δ L L ∧
    |actualWitnessGram f M δ L L/((27/29)*L^2/3)-1|≤R) ∧
    (V≤actualWitnessGram f M δ J J ∧
    |actualWitnessGram f M δ J J/((27/29)*J^2/3)-1|≤R) ∧
    (τ≤1/8 → (174/121)*τ-8*EN≤1-κ) ∧
    (1/8≤τ → τ≤1 → 14703/61952-8*EN≤1-κ) ∧
    -(1/2:ℝ)≤κ ∧ (1/8≤τ → 1/5≤1-κ))

theorem actualPaperKernelConclusions_of_label {b d : ℕ} [NeZero (2^d-1)]
    (hd : 0<d) (g : (LabelField d)ˣ) (hg : orderOf g=2^d-1) (t : Fin b→LabelField d)
    (ht : LinearIndependent (ZMod 2) t)
    (h0 : ∀ a, labelValue t a ≠ 0)
    (hp : Function.Injective (fun z : Sym2 (NonzeroBinary b) => eval t (symLabelProduct z)))
    (hadj : ∀ p q : UnequalLabels b,
      labelValue t p.1.1 * labelValue t q.1.2 ≠
        (g:LabelField d) * (labelValue t p.1.2 * labelValue t q.1.1))
    (hshort : ∀ (p : UnequalLabels b) (j : Fin 4),
      labelValue t p.1.1 ≠ manuscriptShortShifts g j * labelValue t p.1.2)
    {w v : ℝ} (hM : PaperMeshParameters w v b d)
    (hN :
      let K := (paperPeriod d:ℝ)
      let B := (2:ℝ)^b
      let M := paperMeshM v
      let E := paperAtomicCrossSmoothing w K B v M
      paperFarRawBudget B K≤21/500 ∧ E≤1/1000 ∧ paperNearBudget B K E≤1/1000 ∧
        19/50≤paperKernelFloor B K E M)
    {L J : ℝ} (hL : L∈paperScaleWindow) (hJ : J∈paperScaleWindow)
    (hSL : actualSafeLifts hd g hg t L) (hSJ : actualSafeLifts hd g hg t J) :
    ActualPaperKernelConclusions hd g hg t w v L J := by
  let K := (paperPeriod d:ℝ)
  let B := (2:ℝ)^b
  let M := paperMeshM v
  let δ := paperMeshDelta w K v
  let E := paperAtomicCrossSmoothing w K B v M
  let EN := paperNearBudget B K E
  let V := paperKernelFloor B K E M
  let R := paperKernelRelError B K E M
  let T := 48/(29*(M:ℝ)^3)
  let ED := 1/(3*B^2)+2/K+(2/3)*K*δ+manuscriptCrossError B K M
  let EN' := 2/(3*B^2)+2/K+(2/3)*K*δ+manuscriptCrossError B K M
  have eqB : ((2^b:ℕ):ℝ)=B := by dsimp only [B]; norm_cast
  have hKp : 0<K := by
    have T : 0<paperPeriod d := by have := hM.period_lower; omega
    dsimp [K]
    exact_mod_cast T
  have hδ : δ<1/((((2^b:ℕ):ℝ))*K) := by
    rw [eqB]
    refine hM.delta_small.trans_le ?_
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    have hb : 0<B*K := by positivity
    linarith
  have eqN : EN=EN' := by dsimp [EN,EN',E,paperNearBudget,paperAtomicCrossSmoothing]; ring
  have eqV : V=100/261-T/3-ED := by
    dsimp [V,T,ED,E,paperKernelFloor,paperPlateauTail,paperDiagonalBudget,paperAtomicCrossSmoothing]
    ring
  have eqR : R=(T+3*ED)/(100/87) := by
    dsimp [R,T,ED,E,paperKernelRelError,paperPlateauTail,paperDiagonalBudget,paperAtomicCrossSmoothing]
    ring
  have n : EN'≤1/1000 := eqN ▸ hN.2.2.1
  have v' : 19/50≤100/261-T/3-ED := eqV ▸ hN.2.2.2
  have G := actualWitnessGram_complete_kernel_lemma (show 0<b by have := hM.label_ge_two; omega)
    hd g hg t ht hM.label_rank h0 hp hadj hshort M hM.mesh_lt_period hM.mesh_lower
    hM.delta_positive hM.delta_trivial hδ hM.delta_period hM.period_lower hL hJ hSL hSJ
    hN.1 hN.2.1 n v'
  unfold ActualPaperKernelConclusions
  change ((V≤_ ∧ _≤R) ∧ (V≤_ ∧ _≤R) ∧ (_ → _-8*EN≤_) ∧ (_ → _ → _-8*EN≤_) ∧ _)
  rw [eqV,eqR,eqN]
  exact G

theorem paper_all_integer_dimensions_actual_kernel {p w : ℝ} (hp : 0<p) (hw : 4≤w) :
    ∃ d b : ℕ→ℕ,
      (∀ j : ℕ, Tendsto (fun n => (paperPeriod (d n):ℝ)/(paperV p n (d n))^j) atTop atTop) ∧
      (Tendsto (fun n =>
        let v := paperV p n (d n)
        let B := (2:ℝ)^(b n)
        let K := (paperPeriod (d n):ℝ)
        let M := paperMeshM v
        let E := paperAtomicCrossSmoothing w K B v M
        v*paperKernelRelError B K E M) atTop (𝓝 (87/(50*w)))) ∧
      (∀ᶠ n in atTop,
        let v := paperV p n (d n)
        16*Real.log n≤v ∧ v<144*Real.log n ∧ paperV p n (d n+1)<16*Real.log n ∧
        (∀ e : ℕ, 0<e → 16*Real.log n≤paperV p n e → e≤d n) ∧
        PaperMeshParameters w v (b n) (d n) ∧
        ∃ (hd : 0<d n) (hK : NeZero (2^(d n)-1)) (g : (LabelField (d n))ˣ)
          (hg : orderOf g=2^(d n)-1) (t : Fin (b n)→LabelField (d n)),
        LinearIndependent (ZMod 2) t ∧
        ∀ L J : ℝ, L∈paperScaleWindow → J∈paperScaleWindow →
          actualSafeLifts hd g hg t L → actualSafeLifts hd g hg t J →
          @ActualPaperKernelConclusions (b n) (d n) hK hd g hg t w v L J) := by
  obtain ⟨d,hd⟩ := paper_dyadic_choice_eventually hp
  let v (n : ℕ) := paperV p n (d n)
  have hv := paper_v_tendsto (v:=v) (hd.mono fun _ H => H.2.1)
  have hK (j : ℕ) := paper_period_growth_of_choice hp d (hd.mono fun _ H => ⟨H.1,H.2.1,H.2.2.1⟩) j
  obtain ⟨b,hb⟩ := paper_binary_mesh_eventually hw v d hv (hK 4)
  have hK0 : Tendsto (fun n => (paperPeriod (d n):ℝ)) atTop atTop := by simpa using hK 0
  have hK1 : Tendsto (fun n => (paperPeriod (d n):ℝ)/v n) atTop atTop := by
    simpa only [pow_one] using hK 1
  have hb' := paper_actual_kernel_finite_budgets hw hb hv (hK 4) hK0
  have hR := paper_actual_relative_error_scaled hw hb hv (hK 4) hK1
  refine ⟨d,b,hK,hR,?_⟩
  filter_upwards [hd,hb,hb'] with n hn hm H
  refine ⟨hn.2.1,hn.2.2.1,hn.2.2.2.1,hn.2.2.2.2,hm,hn.1,?_⟩
  have nz : NeZero (2^(d n)-1) := ⟨by
    have hP : 1≤paperPeriod (d n) := by have := hm.period_lower; omega
    unfold paperPeriod at hP
    omega⟩
  let _ : NeZero (2^(d n)-1) := nz
  obtain ⟨g,hg,t,ht,h0,hp',hadj,hshort⟩ :=
    actual_manuscript_qualified_labels hm.label_ge_two hm.label_budget
  refine ⟨nz,g,hg,t,ht,?_⟩
  intro L J hL hJ hSL hSJ
  exact actualPaperKernelConclusions_of_label hn.1 g hg t ht h0 hp' hadj hshort hm H hL hJ hSL hSJ

#print axioms actualPaperKernelConclusions_of_label
#print axioms paper_all_integer_dimensions_actual_kernel
end CenteredCubeSqrt
