import PairVarianceStability
import Mathlib.Topology.Algebra.Order.Field
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology ProbabilityTheory
namespace CubeSqrtPair

theorem linear_pair_variance_from_increment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (d e : Ω → ℝ)
    (h2d : MemLp d 2 P) (h2e : MemLp e 2 P)
    (hd0 : ∫ w, d w ∂P = 0) (he0 : ∫ w, e w ∂P = 0) :
    Var[linearPair d e;P] =
      ((∫ w, (d w)^2 ∂P)+(∫ w, (e w)^2 ∂P))/2 - (∫ w, (d w-e w)^2 ∂P)/4 := by
  have hdI := h2d.integrable one_le_two
  have heI := h2e.integrable one_le_two
  have h0 : ∫ w, d w-e w ∂P = 0 := by rw [integral_sub hdI heI,hd0,he0,sub_self]
  have hDif := variance_fun_sub h2d h2e
  have hm : AEMeasurable (fun w ↦ d w-e w) P := (h2d.sub h2e).aemeasurable
  rw [variance_of_integral_eq_zero hm h0,variance_of_integral_eq_zero h2d.aemeasurable hd0,
    variance_of_integral_eq_zero h2e.aemeasurable he0] at hDif
  rw [linear_pair_variance_formula P d e h2d h2e hd0 he0,hDif]
  ring

theorem pair_scaled_sd_squeeze_one (a p q : ℕ → ℝ)
    (ha : Tendsto a atTop (𝓝 0)) (hp : Tendsto p atTop (𝓝 1))
    (h : ∀ᶠ n in atTop,
      Real.sqrt ((1-a n)/(1+a n))*((1-4*a n)*p n) ≤ q n ∧
      q n ≤ Real.sqrt ((1+a n)/(1-a n))*((1+4*a n)*p n)) :
    Tendsto q atTop (𝓝 1) := by
  have hA : Tendsto (fun n ↦ 1-a n) atTop (𝓝 1) := by
    simpa only [sub_zero] using (tendsto_const_nhds (x:=(1:ℝ))).sub ha
  have hB : Tendsto (fun n ↦ 1+a n) atTop (𝓝 1) := by
    simpa only [add_zero] using (tendsto_const_nhds (x:=(1:ℝ))).add ha
  have h4 := ha.const_mul (4:ℝ)
  have hC : Tendsto (fun n ↦ 1-4*a n) atTop (𝓝 1) := by
    simpa only [mul_zero,sub_zero] using (tendsto_const_nhds (x:=(1:ℝ))).sub h4
  have hD : Tendsto (fun n ↦ 1+4*a n) atTop (𝓝 1) := by
    simpa only [mul_zero,add_zero] using (tendsto_const_nhds (x:=(1:ℝ))).add h4
  have hlo := (Real.continuous_sqrt.continuousAt.tendsto.comp
    (hA.div hB (by norm_num : (1:ℝ)≠0))).mul (hC.mul hp)
  have hhi := (Real.continuous_sqrt.continuousAt.tendsto.comp
    (hB.div hA (by norm_num : (1:ℝ)≠0))).mul (hD.mul hp)
  have lo : Tendsto (fun n ↦ Real.sqrt ((1-a n)/(1+a n))*((1-4*a n)*p n)) atTop (𝓝 1) := by
    simpa only [one_div_one,Real.sqrt_one,mul_one,one_mul,Function.comp_apply,Pi.div_apply] using hlo
  have hi : Tendsto (fun n ↦ Real.sqrt ((1+a n)/(1-a n))*((1+4*a n)*p n)) atTop (𝓝 1) := by
    simpa only [one_div_one,Real.sqrt_one,mul_one,one_mul,Function.comp_apply,Pi.div_apply] using hhi
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' lo hi (h.mono fun _ hn ↦ hn.1)
    (h.mono fun _ hn ↦ hn.2)

/-- At any fixed relative distance whose actual scaled squared increment tends
to 0 compared to u², the exact asymmetric pair prefactor tends to the sharp
Gaussian φ(0) coefficient, rather than a uniform but nonsharp constant. -/
theorem actual_pair_sd_ratio_tendsto
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (d e : ℕ → Ω → ℝ) (hmd : ∀ n, Measurable (d n)) (hme : ∀ n, Measurable (e n))
    (a u : ℕ → ℝ) (hN : ℕ → ℕ) (hu : ∀ n, 0 < u n) (ha0 : ∀ n, 0 ≤ a n)
    (ha : Tendsto a atTop (𝓝 0))
    (hd : ∀ n w, |d n w| ≤ a n) (he : ∀ n w, |e n w| ≤ a n)
    (hd0 : ∀ n, ∫ w, d n w ∂P = 0) (he0 : ∀ n, ∫ w, e n w ∂P = 0)
    (hCov : ∀ᶠ n in atTop,
      -Real.sqrt (∫ w, (d n w)^2 ∂P)*Real.sqrt (∫ w, (e n w)^2 ∂P)/2 ≤ cov[d n,e n;P])
    (hDy : Tendsto (fun n ↦ (hN n:ℝ)*(∫ w, (d n w)^2 ∂P)/(u n)^2) atTop (𝓝 1))
    (hDz : Tendsto (fun n ↦ (hN n:ℝ)*(∫ w, (e n w)^2 ∂P)/(u n)^2) atTop (𝓝 1))
    (hDiff : Tendsto (fun n ↦ (hN n:ℝ)*(∫ w, (d n w-e n w)^2 ∂P)/(u n)^2) atTop (𝓝 0)) :
    Tendsto (fun n ↦ u n/(Real.sqrt (hN n:ℝ)*
      Real.sqrt (Var[logPair (d n) (e n);P.tilted (logPair (d n) (e n))]))) atTop (𝓝 1) := by
  let T (n : ℕ) := linearPair (d n) (e n)
  let V (n : ℕ) := logPair (d n) (e n)
  let p (n : ℕ) := Real.sqrt (hN n:ℝ)*Real.sqrt (Var[T n;P])/u n
  let q (n : ℕ) := Real.sqrt (hN n:ℝ)*Real.sqrt (Var[V n;P.tilted (V n)])/u n
  have h2d (n : ℕ) : MemLp (d n) 2 P := MemLp.of_bound (hmd n).aestronglyMeasurable (a n)
    (Eventually.of_forall fun w ↦ by simpa only [Real.norm_eq_abs] using hd n w)
  have h2e (n : ℕ) : MemLp (e n) 2 P := MemLp.of_bound (hme n).aestronglyMeasurable (a n)
    (Eventually.of_forall fun w ↦ by simpa only [Real.norm_eq_abs] using he n w)
  have hP2 : Tendsto (fun n ↦ (p n)^2) atTop (𝓝 1) := by
    have H := (((hDy.add hDz).div_const 2).sub (hDiff.div_const 4))
    have hH : Tendsto (fun n ↦
        (((hN n:ℝ)*(∫ w, (d n w)^2 ∂P)/(u n)^2)+((hN n:ℝ)*(∫ w, (e n w)^2 ∂P)/(u n)^2))/2 -
        ((hN n:ℝ)*(∫ w, (d n w-e n w)^2 ∂P)/(u n)^2)/4) atTop (𝓝 1) := by
      norm_num at H ⊢
      exact H
    apply hH.congr
    intro n
    dsimp [p,T]
    rw [div_pow,mul_pow,Real.sq_sqrt (Nat.cast_nonneg _),Real.sq_sqrt (variance_nonneg _ _),
      linear_pair_variance_from_increment P (d n) (e n) (h2d n) (h2e n) (hd0 n) (he0 n)]
    ring
  have hp : Tendsto p atTop (𝓝 1) := by
    have H := Real.continuous_sqrt.continuousAt.tendsto.comp hP2
    rw [Real.sqrt_one] at H
    apply H.congr
    intro n
    change Real.sqrt ((p n)^2) = p n
    apply Real.sqrt_sq
    exact div_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) (hu n).le
  have hq : Tendsto q atTop (𝓝 1) := by
    apply pair_scaled_sd_squeeze_one a p q ha hp
    filter_upwards [ha.eventually_lt_const (by norm_num : (0:ℝ)<1/2),hCov] with n hn hc
    have hLin := linear_pair_variance_lower P (d n) (e n) (h2d n) (h2e n) (hd0 n) (he0 n) hc
    have H := actual_logPair_sqrt_variance_sandwich P (d n) (e n) (hmd n) (hme n)
      (a n) (ha0 n) hn.le (hd n) (he n) hLin
    let R := Real.sqrt (hN n:ℝ)/u n
    have hR : 0 ≤ R := div_nonneg (Real.sqrt_nonneg _) (hu n).le
    constructor
    · have hh := mul_le_mul_of_nonneg_left H.1 hR
      dsimp [p,q,T,V,R] at hh ⊢
      convert hh using 1 <;> ring
    · have hh := mul_le_mul_of_nonneg_left H.2 hR
      dsimp [p,q,T,V,R] at hh ⊢
      convert hh using 1 <;> ring
  have H := hq.inv₀ (by norm_num : (1:ℝ)≠0)
  rw [inv_one] at H
  apply H.congr
  intro n
  simp only [q,inv_div,V]

end CubeSqrtPair
#print axioms CubeSqrtPair.actual_pair_sd_ratio_tendsto
