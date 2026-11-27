import ActualPaperPairBound
import SqrtAllIntegerPackets

namespace CenteredCubeSqrt
open MeasureTheory ProbabilityTheory Set Filter MvPolynomial CubeBrownian CubeSqrtProbability
open scoped ProbabilityTheory Interval
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
set_option maxHeartbeats 2200000

theorem actual_pair_probability_from_kernel {b d : ℕ} [NeZero (2^d-1)]
    (hd : 0<d) (g : (LabelField d)ˣ) (hg : orderOf g=2^d-1) (t : Fin b → LabelField d)
    (M : ℕ) {δ L J : ℝ} (hδ : 0<δ)
    (hδB : δ<1/((((2^b:ℕ):ℝ))*(((2^d-1:ℕ):ℝ))))
    (hK : 18≤(2^d-1:ℕ)) (hL : L∈Icc (10/9:ℝ) (11/9)) (hJ : J∈Icc (10/9:ℝ) (11/9))
    (hKernel :
      let K := ((2^d-1:ℕ):ℝ)
      let B := (2:ℝ)^b
      let f := ordinalPhaseLabel hd g hg t
      let κ := actualNormalizedGram f M δ L J
      let τ := K*|J-L|/2
      (0<actualWitnessGram f M δ L L ∧
        |actualWitnessGram f M δ L L/((27/29)*L^2/3)-1|≤actualPairRelativeError B K M δ) ∧
      (0<actualWitnessGram f M δ J J ∧
        |actualWitnessGram f M δ J J/((27/29)*J^2/3)-1|≤actualPairRelativeError B K M δ) ∧
      (τ≤1/8 → (174/121)*τ-8*actualPairNearError B K M δ≤1-κ) ∧
      -(1/2:ℝ)≤κ ∧ (1/8≤τ → 1/5≤1-κ))
    {n : ℕ} (hn : 0<n) {p u v C h : ℝ} (hP : 0<p) (hu : 0<u) (huv : u^2=v)
    (hv : v=(n:ℝ)*(p/(((2^d-1:ℕ):ℝ)))^2*(9/29))
    (ha : 7*p/(((2^d-1:ℕ):ℝ))≤1/8)
    (hC : v*actualPairRelativeError ((2:ℝ)^b) (((2^d-1:ℕ):ℝ)) M δ≤C)
    (hFac : 4*v/5≤(v-C)/(1+7*p/(((2^d-1:ℕ):ℝ))))
    (hNearErr : 8*v*actualPairNearError ((2:ℝ)^b) (((2^d-1:ℕ):ℝ)) M δ≤2) :
    let K := ((2^d-1:ℕ):ℝ)
    let f := ordinalPhaseLabel hd g hg t
    let τ := K * |J-L|/2
    let PiLaw := actualPaperProductLaw n
    let E₁ := actualPaperScaleEvent f M n p δ h L
    let E₂ := actualPaperScaleEvent f M n p δ h J
    ((τ≤1/8 → u*Real.exp h*PiLaw.real (E₁∩E₂) ≤
      actualPairPrefactor * Real.exp (1/4) * Real.exp (-(174/121/8)*(v*τ))) ∧
    (1/8≤τ → u*Real.exp h*PiLaw.real (E₁∩E₂) ≤ actualPairPrefactor * Real.exp (-v/25))) := by
  let K := ((2^d-1:ℕ):ℝ)
  let B := (2:ℝ)^b
  let f := ordinalPhaseLabel hd g hg t
  let a := 7*p/K
  let d₁ := actualWindowPerturbation f M p δ L
  let d₂ := actualWindowPerturbation f M p δ J
  let κ := actualNormalizedGram f M δ L J
  let τ := K * |J-L|/2
  let H := CubeSqrtPair.avgAffinity unitPeriodLaw (fun w => Real.log (1+d₁ w)) (fun w => Real.log (1+d₂ w))
  let Θ := (v-C)/(1+a)
  have hvp : 0<v := huv ▸ sq_pos_of_pos hu
  have hp0 : (0:ℝ)≤p := hP.le
  have a0 : 0≤a := by unfold a K; positivity
  have hhB : 0<(2^b:ℕ) := by positivity
  have iL : 1≤L := by linarith [hL.1]
  have iJ : 1≤J := by linarith [hJ.1]
  have pL : 0<L := by linarith
  have pJ : 0<J := by linarith
  have hhK : 2≤(2^d-1:ℕ) := by omega
  have capL : ∀ x, |d₁ x|≤a := actual_windowPerturbation_uniform_cap f M hhB hhK hp0 hδ hδB iL
  have capJ : ∀ x, |d₂ x|≤a := actual_windowPerturbation_uniform_cap f M hhB hhK hp0 hδ hδB iJ
  have zL : (∫ x, d₁ x ∂unitPeriodLaw)=0 := by
    rw [unitPeriod_integral]
    exact actualWindowPerturbation_integral_zero f M p hhB hhK hδ hδB pL
  have zJ : (∫ x, d₂ x ∂unitPeriodLaw)=0 := by
    rw [unitPeriod_integral]
    exact actualWindowPerturbation_integral_zero f M p hhB hhK hδ hδB pJ
  obtain ⟨D1,D2,N,Clo,F⟩ := hKernel
  have gL : 0<actualWitnessGram f M δ L L := D1.1
  have gJ : 0<actualWitnessGram f M δ J J := D2.1
  have Ctop : κ≤1 := actual_normalizedGram_le_one_from_positive f M hδ L J gL gJ
  have qL := actual_pair_moment_lower_of_relative f M n p δ pL hv hvp.le hC D1.2
  have qJ := actual_pair_moment_lower_of_relative f M n p δ pJ hv hvp.le hC D2.2
  have θ0 : 0<1+a := by linarith
  have θL : v/2≤Θ := by change 4*v/5≤Θ at hFac; linarith
  have vC : v/2≤v-C := by
    have hθ := (le_div_iff₀ θ0).1 θL
    have hn := mul_nonneg (show 0≤v/2 by positivity) a0
    linarith only [hθ,hn]
  have cov := actual_paper_pair_cov_normalized f M n hP hhB hhK hδ hδB pL pJ capL capJ gL gJ
  have hh := CubeSqrtPair.paper_allpairs_finite unitPeriodLaw d₁ d₂
    (actual_windowPerturbation_continuous f M p hδ pL).measurable
    (actual_windowPerturbation_continuous f M p hδ pJ).measurable
    a a0 ha capL capJ zL zJ hn h u v C
    (actualPaperPairMoment f M n p δ L) (actualPaperPairMoment f M n p δ J) κ hu huv
    vC (by change -(1/2:ℝ)≤κ at Clo; linarith only [Clo]) Ctop (actual_paper_pair_moment_eq f M n p hδ pL)
    (actual_paper_pair_moment_eq f M n p hδ pJ) qL qJ cov
  let X := u*Real.exp h*(actualPaperProductLaw n).real
    (actualPaperScaleEvent f M n p δ h L∩actualPaperScaleEvent f M n p δ h J)
  have A : X ≤ actualPairPrefactor*H^n := hh.1
  have Expo : H^n≤Real.exp (-(Θ*(1-κ)/4)) := by
    refine hh.2.trans_eq ?_
    congr 1
    unfold Θ
    field_simp [θ0.ne'] <;> ring
  change (τ≤1/8 → X ≤ _) ∧ (1/8≤τ → X ≤ _)
  constructor
  · intro hτ
    have hN : (174/121)*τ-8*actualPairNearError B K M δ≤1-κ := N hτ
    have hN' := mul_le_mul_of_nonneg_left hN hvp.le
    have hNear : (174/121)*(v*τ)-2 ≤ v*(1-κ) := by
      change 8*v*actualPairNearError B K M δ≤2 at hNearErr
      nlinarith only [hN',hNearErr]
    have R := CubeSqrtPair.kernel_near_decay H Θ v κ (v*τ) (174/121) 2 n hvp θL Ctop hNear Expo
    have RW := mul_le_mul_of_nonneg_left R actual_pairPrefactor_nonneg
    refine A.trans (RW.trans_eq ?_)
    rw [show (2:ℝ)/8=1/4 by norm_num, show -(174/121:ℝ)*(v*τ)/8=-(174/121/8)*(v*τ) by ring]
    ring
  · intro hτ
    have HH := CubeSqrtPair.kernel_middle_far_decay H Θ v κ n hvp.le hFac (F hτ) Expo
    exact A.trans (mul_le_mul_of_nonneg_left HH actual_pairPrefactor_nonneg)

#print axioms actual_pair_probability_from_kernel
end CenteredCubeSqrt
