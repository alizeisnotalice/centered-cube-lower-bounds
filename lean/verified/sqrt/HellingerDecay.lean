import AffinityTransfer
import Mathlib.Tactic
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology ProbabilityTheory
namespace CubeSqrtPair

/-- Exactly the Hellinger distance identity and bounded-density deficit used
in the √n manuscript; no correlation or approximate tilt is assumed. -/
theorem hellinger_deficit_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y Z : Ω → ℝ) (hY : Measurable Y) (hZ : Measurable Z)
    (hYI : Integrable Y P) (hZI : Integrable Z P)
    (hYn : ∫ w, Y w ∂P = 1) (hZn : ∫ w, Z w ∂P = 1)
    (a : ℝ) (ha : 0 ≤ a)
    (hYp : ∀ w, 0 < Y w) (hZp : ∀ w, 0 < Z w)
    (hYb : ∀ w, Y w ≤ 1+a) (hZb : ∀ w, Z w ≤ 1+a) :
    let H := ∫ w, Real.sqrt (Y w*Z w) ∂P
    Integrable (fun w ↦ Real.sqrt (Y w*Z w)) P ∧ 0 < H ∧ H ≤ 1 ∧
      (∫ w, (Y w-Z w)^2 ∂P)/(8*(1+a)) ≤ 1-H := by
  dsimp only
  let R (w : Ω) := Real.sqrt (Y w*Z w)
  let F (w : Ω) := (Real.sqrt (Y w)-Real.sqrt (Z w))^2
  let H := ∫ w, R w ∂P
  have hRm : Measurable R := Real.continuous_sqrt.measurable.comp (hY.mul hZ)
  have hR (w : Ω) : R w = Real.sqrt (Y w)*Real.sqrt (Z w) := Real.sqrt_mul (hYp w).le _
  have hF (w : Ω) : F w = Y w+Z w-2*R w := by
    unfold F
    rw [sub_sq,Real.sq_sqrt (hYp w).le,Real.sq_sqrt (hZp w).le,hR w]
    ring
  have hRI : Integrable R P := by
    apply (((hYI.add hZI).div_const 2)).mono' hRm.aestronglyMeasurable
    exact Eventually.of_forall fun w ↦ by
      rw [Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
      have h := sq_nonneg (Real.sqrt (Y w)-Real.sqrt (Z w))
      change 0 ≤ F w at h
      rw [hF] at h
      change R w ≤ (Y w+Z w)/2
      linarith only [h]
  have hHp : 0 < H := by
    have hLog : Integrable (fun w ↦ Real.exp (pairScore (fun t ↦ Real.log (Y t)) (fun t ↦ Real.log (Z t)) w)) P := by
      apply hRI.congr
      exact Eventually.of_forall fun w ↦ by
        dsimp only [pairScore,R]
        rw [← Real.log_mul (hYp w).ne' (hZp w).ne',Real.sqrt_eq_rpow,
          Real.rpow_def_of_pos (mul_pos (hYp w) (hZp w))]
        congr 1
        ring
    change 0 < (∫ w, Real.sqrt (Y w*Z w) ∂P)
    rw [← avgAffinity_eq_hellinger P Y Z hYp hZp]
    simpa only [avgAffinity,mgf,one_mul] using
      (mgf_pos (μ:=P) (t:=1) (by simpa only [one_mul] using hLog))
  have hDInt : Integrable F P := by
    apply ((hYI.add hZI).sub (hRI.const_mul 2)).congr
    exact Eventually.of_forall fun w ↦ (hF w).symm
  have hFInt : (∫ w, F w ∂P) = 2*(1-H) := by
    simp_rw [hF]
    have hSum : Integrable (fun w ↦ Y w+Z w) P := hYI.add hZI
    have hMul : Integrable (fun w ↦ 2*R w) P := hRI.const_mul 2
    rw [integral_sub hSum hMul,integral_add hYI hZI,integral_const_mul,hYn,hZn]
    change 1+1-2*H = _
    ring
  have hH1 : H ≤ 1 := by
    have h : 0 ≤ ∫ w, F w ∂P := integral_nonneg (fun w ↦ sq_nonneg (Real.sqrt (Y w)-Real.sqrt (Z w)))
    change 0 ≤ ∫ w, F w ∂P at h
    rw [hFInt] at h
    linarith only [h]
  have hPt (w : Ω) : (Y w-Z w)^2 ≤ (4*(1+a))*F w := by
    have hs : Real.sqrt (Y w)+Real.sqrt (Z w) ≤ 2*Real.sqrt (1+a) := by
      linarith only [Real.sqrt_le_sqrt (hYb w),Real.sqrt_le_sqrt (hZb w)]
    have hs2 := pow_le_pow_left₀
      (add_nonneg (Real.sqrt_nonneg (Y w)) (Real.sqrt_nonneg (Z w))) hs 2
    rw [mul_pow,Real.sq_sqrt (by positivity : 0 ≤ 1+a)] at hs2
    have he : Y w-Z w =
        (Real.sqrt (Y w)-Real.sqrt (Z w))*(Real.sqrt (Y w)+Real.sqrt (Z w)) := by
      calc
        _ = (Real.sqrt (Y w))^2 - (Real.sqrt (Z w))^2 := by simp [Real.sq_sqrt,(hYp w).le,(hZp w).le]
        _ = _ := by ring
    rw [he,mul_pow,mul_comm (4*(1+a))]
    exact mul_le_mul_of_nonneg_left (by simpa only [show (2:ℝ)^2=4 by norm_num] using hs2) (sq_nonneg _)
  have hB : (∫ w, (Y w-Z w)^2 ∂P) ≤ (4*(1+a))*(2*(1-H)) := by
    calc
      _ ≤ ∫ w, (4*(1+a))*F w ∂P := integral_mono_of_nonneg
        (Eventually.of_forall fun _ ↦ sq_nonneg _) (hDInt.const_mul _) (Eventually.of_forall hPt)
      _ = _ := by rw [integral_const_mul,hFInt]
  refine ⟨hRI,hHp,hH1,(div_le_iff₀ (by positivity)).2 ?_⟩
  convert hB using 1 <;> ring

theorem hellinger_pow_le_exp_deficit (H : ℝ) (hH : 0 ≤ H) (n : ℕ) :
    H^n ≤ Real.exp (-(n:ℝ)*(1-H)) := by
  have hE : H ≤ Real.exp (H-1) := by
    have h := Real.add_one_le_exp (H-1)
    linarith only [h]
  have h := pow_le_pow_left₀ hH hE n
  rw [← Real.exp_nat_mul] at h
  convert h using 2 <;> ring

end CubeSqrtPair
#print axioms CubeSqrtPair.hellinger_deficit_bound
#print axioms CubeSqrtPair.hellinger_pow_le_exp_deficit
