import HellingerDecay
import PairBoundedSource
import Mathlib.Probability.Moments.Variance

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology ProbabilityTheory
namespace CubeSqrtPair

theorem kernel_affinity_exp_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (d e : Ω → ℝ) (hmd : Measurable d) (hme : Measurable e)
    (a : ℝ) (ha0 : 0 ≤ a) (ha : a ≤ 1/2)
    (hd : ∀ w, |d w| ≤ a) (he : ∀ w, |e w| ≤ a)
    (hd0 : ∫ w, d w ∂P = 0) (he0 : ∫ w, e w ∂P = 0)
    (n : ℕ) (qY qZ v C κ : ℝ) (hκ : κ ≤ 1) (hvc : 0 ≤ v-C)
    (hqY : qY = (n:ℝ)*(∫ w, (d w)^2 ∂P))
    (hqZ : qZ = (n:ℝ)*(∫ w, (e w)^2 ∂P))
    (hYlo : v-C ≤ qY) (hZlo : v-C ≤ qZ)
    (hCov : (n:ℝ)*cov[d,e;P] = Real.sqrt qY*Real.sqrt qZ*κ) :
    (avgAffinity P (fun w ↦ Real.log (1+d w)) (fun w ↦ Real.log (1+e w)))^n ≤
      Real.exp (-((v-C)*(1-κ)/(4*(1+a)))) := by
  let Y := fun w ↦ 1+d w
  let Z := fun w ↦ 1+e w
  let H := ∫ w, Real.sqrt (Y w*Z w) ∂P
  have h2d : MemLp d 2 P := MemLp.of_bound hmd.aestronglyMeasurable a
    (Eventually.of_forall fun w ↦ by simpa only [Real.norm_eq_abs] using hd w)
  have h2e : MemLp e 2 P := MemLp.of_bound hme.aestronglyMeasurable a
    (Eventually.of_forall fun w ↦ by simpa only [Real.norm_eq_abs] using he w)
  have hId := h2d.integrable one_le_two
  have hIe := h2e.integrable one_le_two
  have hYI : Integrable Y P := (integrable_const (1:ℝ)).add hId
  have hZI : Integrable Z P := (integrable_const (1:ℝ)).add hIe
  have hY1 : ∫ w, Y w ∂P = 1 := by
    unfold Y
    rw [integral_add (integrable_const _) hId,hd0]
    simp
  have hZ1 : ∫ w, Z w ∂P = 1 := by
    unfold Z
    rw [integral_add (integrable_const _) hIe,he0]
    simp
  have hYp (w : Ω) : 0 < Y w := by dsimp [Y]; linarith only [ha,(abs_le.mp (hd w)).1]
  have hZp (w : Ω) : 0 < Z w := by dsimp [Z]; linarith only [ha,(abs_le.mp (he w)).1]
  have hYu (w : Ω) : Y w ≤ 1+a := by dsimp [Y]; linarith only [(abs_le.mp (hd w)).2]
  have hZu (w : Ω) : Z w ≤ 1+a := by dsimp [Z]; linarith only [(abs_le.mp (he w)).2]
  have hh := hellinger_deficit_bound P Y Z (hmd.const_add _) (hme.const_add _)
    hYI hZI hY1 hZ1 a ha0 hYp hZp hYu hZu
  have hDYZ : (fun w ↦ (Y w-Z w)^2) = fun w ↦ (d w-e w)^2 := by
    funext w
    dsimp [Y,Z]
    ring
  have hDiff := variance_fun_sub h2d h2e
  have hz : (∫ w, d w-e w ∂P) = 0 := by rw [integral_sub hId hIe,hd0,he0,sub_self]
  have hm : AEMeasurable (fun w ↦ d w-e w) P := (hmd.sub hme).aemeasurable
  rw [variance_of_integral_eq_zero hm hz,variance_of_integral_eq_zero hmd.aemeasurable hd0,
    variance_of_integral_eq_zero hme.aemeasurable he0] at hDiff
  have hEq : (n:ℝ)*(∫ w, (Y w-Z w)^2 ∂P) = qY+qZ-2*Real.sqrt qY*Real.sqrt qZ*κ := by
    rw [hDYZ,hDiff]
    calc
      _ = (n:ℝ)*(∫ w, (d w)^2 ∂P)+(n:ℝ)*(∫ w, (e w)^2 ∂P)-2*((n:ℝ)*cov[d,e;P]) := by ring
      _ = _ := by rw [← hqY,← hqZ,hCov]; ring
  have hqY0 : 0 ≤ qY := hvc.trans hYlo
  have hqZ0 : 0 ≤ qZ := hvc.trans hZlo
  have hS : v-C ≤ Real.sqrt qY * Real.sqrt qZ := by
    calc
      _ = Real.sqrt (v-C)*Real.sqrt (v-C) := (Real.mul_self_sqrt hvc).symm
      _ ≤ _ := mul_le_mul (Real.sqrt_le_sqrt hYlo) (Real.sqrt_le_sqrt hZlo)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg qY)
  have hDlow : 2*(v-C)*(1-κ) ≤ (n:ℝ)*(∫ w, (Y w-Z w)^2 ∂P) := by
    have hS2 := mul_le_mul_of_nonneg_right hS (sub_nonneg.mpr hκ)
    rw [hEq]
    nlinarith only [hS2,sq_nonneg (Real.sqrt qY-Real.sqrt qZ),Real.sq_sqrt hqY0,Real.sq_sqrt hqZ0]
  have hDef : ((v-C)*(1-κ))/(4*(1+a)) ≤ (n:ℝ)*(1-H) := by
    have hA : 0 < 1+a := by positivity
    have hB : 0 < 8*(1+a) := by positivity
    have h := mul_le_mul_of_nonneg_left hh.2.2.2 (Nat.cast_nonneg n)
    have h' : (n:ℝ)*((∫ w, (Y w-Z w)^2 ∂P)/(8*(1+a))) ≤ (n:ℝ)*(1-H) := h
    rw [← mul_div_assoc] at h'
    have h2 := div_le_div_of_nonneg_right hDlow hB.le
    have heq : 2*(v-C)*(1-κ)/(8*(1+a)) = (v-C)*(1-κ)/(4*(1+a)) := by field_simp [hA.ne'] <;> ring
    rw [heq] at h2
    exact h2.trans h'
  change (avgAffinity P (fun w ↦ Real.log (Y w)) (fun w ↦ Real.log (Z w)))^n ≤ _
  rw [avgAffinity_eq_hellinger P Y Z hYp hZp]
  exact (hellinger_pow_le_exp_deficit H hh.2.1.le n).trans
    (Real.exp_le_exp.mpr (by linarith only [hDef]))

/-- The middle/far phase falls directly out of the exact kernel affinity
formula once the correlation gap and variance factor lower bounds hold. -/
theorem kernel_middle_far_decay (H θ v κ : ℝ) (n : ℕ) (hv : 0 ≤ v)
    (hθ : 4*v/5 ≤ θ) (hκ : 1/5 ≤ 1-κ)
    (hH : H^n ≤ Real.exp (- (θ*(1-κ)/4))) :
    H^n ≤ Real.exp (-v/25) := by
  apply hH.trans (Real.exp_le_exp.mpr _)
  have hh := mul_le_mul hθ hκ (by positivity : (0:ℝ) ≤ 1/5) (le_trans (by positivity) hθ)
  linarith only [hh]

/-- Near-field envelope for growing r. D is the explicit uniform kernel
error at scale 1/w plus any remaining o(1) term. -/
theorem kernel_near_decay (H θ v κ r c D : ℝ) (n : ℕ)
    (hv : 0 < v) (hθ : v/2 ≤ θ) (hκ : κ ≤ 1)
    (hgap : c*r-D ≤ v*(1-κ))
    (hH : H^n ≤ Real.exp (-(θ*(1-κ)/4))) :
    H^n ≤ Real.exp (D/8)*Real.exp (-c*r/8) := by
  rw [← Real.exp_add]
  apply hH.trans (Real.exp_le_exp.mpr _)
  have hh := mul_le_mul_of_nonneg_right hθ (sub_nonneg.mpr hκ)
  linarith only [hh,hgap]

end CubeSqrtPair
#print axioms CubeSqrtPair.kernel_affinity_exp_bound
#print axioms CubeSqrtPair.kernel_middle_far_decay
#print axioms CubeSqrtPair.kernel_near_decay
