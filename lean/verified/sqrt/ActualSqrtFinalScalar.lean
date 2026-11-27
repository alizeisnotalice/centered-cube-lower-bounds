import SqrtManuscriptStatements
import PaperPairGlobalGap
import BrownianExpectation

open Filter CenteredCubeSqrt
open scoped Topology ENNReal
namespace CubeBrownian

theorem paper_phi_zero : φ 0 = 1 / Real.sqrt (2*Real.pi) := by
  unfold φ
  rw [ProbabilityTheory.gaussianPDFReal_def]
  norm_num [one_div]

noncomputable def paperMeshPeriod (T : ℕ) : ℝ := T+paperPairPacketGap T

noncomputable def paperLowerCoeff (p η : ℝ) (T : ℕ) : ℝ :=
  (paperCp p/(2*paperMeshPeriod T))*(φ 0*(T:ℝ)*(29/110-η/9)) -
    paperPairGlobalEnvelope p (paperMeshPeriod T) (paperPairPacketGap T) (T^3)

theorem paper_lower_coefficient_tendsto (p η : ℝ) (hp : 0<p) :
    Tendsto (paperLowerCoeff p η) atTop
      (𝓝 (p*CubeSqrtEnd.paperConstant - ((paperCp p)/2*φ 0/9)*η)) := by
  have hD := paper_pair_packet_gap_ratio.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hG : Tendsto (fun T : ℕ => 1+paperPairPacketGap (T:ℝ)/(T:ℝ)) atTop (𝓝 1) := by
    simpa only [Function.comp_apply,add_zero] using hD.const_add (1:ℝ)
  have ht : Tendsto (fun T : ℕ => (T:ℝ)/paperMeshPeriod T) atTop (𝓝 1) := by
    have hh := hG.inv₀ (one_ne_zero : (1:ℝ)≠0)
    simp only [inv_one] at hh
    refine hh.congr' ?_
    filter_upwards [eventually_gt_atTop (1:ℕ)] with T hT
    have hT1 : 1<(T:ℝ) := by exact_mod_cast hT
    have hD0 := paper_pair_packet_gap_positive hT1
    unfold paperMeshPeriod
    field_simp [show (T:ℝ)≠0 by positivity,
      show (T:ℝ)+paperPairPacketGap (T:ℝ)≠0 by linarith]
    <;> ring
  have hbase : paperCp p/2*φ 0*(29/110) = p*CubeSqrtEnd.paperConstant := by
    rw [paper_phi_zero]
    have h := CubeSqrtEnd.paper_constant_from_density p
    rw [CubeSqrtEnd.paper_intensity_integral] at h
    unfold paperCp
    rw [← h]
    ring
  have hconst : paperCp p/2*φ 0*((29:ℝ)/110-η/9) =
      p*CubeSqrtEnd.paperConstant-(paperCp p/2*φ 0/9)*η := by
    rw [← hbase]
    ring
  have hO := paper_pair_global_gap_tendsto hp
  have h := (ht.const_mul (paperCp p/2*φ 0*((29:ℝ)/110-η/9))).sub hO
  simp only [mul_one,sub_zero] at h
  have H : Tendsto (paperLowerCoeff p η) atTop
      (𝓝 (paperCp p/2*φ 0*((29:ℝ)/110-η/9))) := by
    refine h.congr' (Eventually.of_forall (fun T => ?_))
    unfold paperLowerCoeff
    rw [←div_div]
    unfold paperMeshPeriod
    ring
  rwa [hconst] at H

/-- Specialized final scalar extraction using the exact manuscript leading
constant and a vanishing outer overlap. The sole input is an actual
finite-parameter lower bound, ready to accept the verified uniform winner. -/
theorem exact_main_from_actual_finite_grid
    (hf : ∀ p : ℝ, 0<p → p<1 → ∀ η : ℝ, 0<η →
      ∀ᶠ T : ℕ in atTop, ∀ b : ℝ, 0<b → b<paperLowerCoeff p η T →
        ∀ᶠ n : ℕ in atTop, ENNReal.ofReal (b*Real.sqrt (n:ℝ)) ≤ CenteredCube.weakConstant n) :
    CenteredCube.SqrtManuscriptMain := by
  apply CenteredCube.sqrt_manuscript_scope_iff.2
  apply CenteredCube.sqrtNormalizedWeakConstant_liminf_ge CubeSqrtEnd.paperConstant_pos
  intro b hb hbc
  let C := CubeSqrtEnd.paperConstant
  have hC : 0<C := CubeSqrtEnd.paperConstant_pos
  let p := (b/C+1)/2
  have hbc' : b/C < 1 := (div_lt_one hC).2 hbc
  have hp : 0<p := by dsimp [p]; positivity
  have hp1 : p<1 := by dsimp [p]; linarith
  have hbp : b<p*C := by
    apply (div_lt_iff₀ hC).1
    dsimp [p]
    linarith
  let S := paperCp p/2*φ 0/9
  let η := (p*C-b)/(2*(|S|+1))
  have hη : 0<η := div_pos (sub_pos.2 hbp) (by positivity)
  have hsmall : S*η ≤ (p*C-b)/2 := by
    have hS : S ≤ |S|+1 := by linarith [le_abs_self S]
    calc
      _ ≤ (|S|+1)*η := mul_le_mul_of_nonneg_right hS hη.le
      _ = _ := by
        dsimp [η]
        field_simp [show |S|+1≠0 by positivity]
  have hcmp : b < p*CubeSqrtEnd.paperConstant-S*η := by
    change b < p*C-S*η
    linarith
  obtain ⟨T,ht,htb⟩ := ((hf p hp hp1 η hη).and
    ((paper_lower_coefficient_tendsto p η hp).eventually_const_lt hcmp)).exists
  exact ht b hb htb

#print axioms paper_lower_coefficient_tendsto
#print axioms exact_main_from_actual_finite_grid
end CubeBrownian
