import TrueTiltPeriod
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.Independence.Basic

open MeasureTheory ProbabilityTheory Set
namespace CubeSqrtProbability

/-- The tilt by a sum of identical one-coordinate scores is exactly the
product of the normalized one-coordinate tilts. -/
theorem true_product_tilt_eq_general
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (f : Ω → ℝ)
    (hf : Integrable (fun w ↦ Real.exp (f w)) P) :
    (Measure.pi (fun _ : ι ↦ P)).tilted (fun x ↦ ∑ i, f (x i)) =
      Measure.pi (fun _ : ι ↦ P.tilted f) := by
  classical
  let Q := P.tilted f
  letI : IsProbabilityMeasure Q := isProbabilityMeasure_tilted hf
  let h : ℝ := ∫ w, Real.exp (f w) ∂P
  have hNormPi : (∫ x : ι → Ω, Real.exp (∑ i, f (x i)) ∂(Measure.pi fun _ : ι ↦ P))=
      h ^ Fintype.card ι := by
    simp_rw [Real.exp_sum]
    exact integral_fintype_prod_eq_pow (ι := ι) (μ := P) (fun w ↦ Real.exp (f w))
  symm
  apply Measure.pi_eq
  intro s hs
  have hsPi : MeasurableSet (pi univ s) := MeasurableSet.pi (Set.to_countable _) fun i _ ↦ hs i
  change (Measure.pi (fun _ : ι ↦ P)).tilted (fun x ↦ ∑ i, f (x i)) (pi univ s) =
    ∏ i, Q (s i)
  rw [tilted_apply_eq_ofReal_integral' _ hsPi, hNormPi]
  have hdiv (x : ι → Ω) : Real.exp (∑ i, f (x i)) / h^Fintype.card ι =
      ∏ i, Real.exp (f (x i))/h := by
    rw [Real.exp_sum, Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ]
  simp_rw [hdiv]
  have hL : (∫ x in pi univ s, ∏ i, (Real.exp (f (x i))/h) ∂(Measure.pi fun _ : ι ↦ P)) =
      ∏ i, (∫ w in s i, (Real.exp (f w)/h) ∂P) := by
    rw [show (∫ x in pi univ s, ∏ i, (Real.exp (f (x i))/h) ∂(Measure.pi fun _ : ι ↦ P)) =
      (∫ x, (pi univ s).indicator (fun x : ι → Ω ↦ ∏ i, (Real.exp (f (x i))/h)) x
        ∂(Measure.pi fun _ : ι ↦ P)) from (integral_indicator hsPi).symm]
    have he : (pi univ s).indicator (fun x : ι → Ω ↦ ∏ i, (Real.exp (f (x i))/h)) =
        fun x ↦ ∏ i, (s i).indicator (fun w ↦ (Real.exp (f w)/h)) (x i) := by
      funext x
      by_cases hm : x ∈ pi univ s
      · rw [indicator_of_mem hm]
        apply Finset.prod_congr rfl
        intro i _
        rw [indicator_of_mem (mem_univ_pi.mp hm i)]
      · rw [indicator_of_notMem hm]
        rcases not_forall.mp (mt mem_univ_pi.mpr hm) with ⟨i,hi⟩
        symm
        exact Finset.prod_eq_zero (Finset.mem_univ i)
          (show (s i).indicator (fun w ↦ Real.exp (f w)/h) (x i) = (0:ℝ) from
            indicator_of_notMem hi _)
    rw [he, integral_fintype_prod_eq_prod]
    apply Finset.prod_congr rfl
    intro i _
    exact integral_indicator (hs i)
  rw [hL, ENNReal.ofReal_prod_of_nonneg (fun i _ ↦ integral_nonneg fun w ↦ div_nonneg (Real.exp_nonneg _) (integral_nonneg fun _ ↦ Real.exp_nonneg _))]
  apply Finset.prod_congr rfl
  intro i _
  change ENNReal.ofReal (∫ w in s i, Real.exp (f w)/h ∂P) = P.tilted f (s i)
  rw [tilted_apply_eq_ofReal_integral' _ (hs i)]

/-- Genuine independence of the tilted coordinate score vectors. -/
theorem true_winner_tilt_independent
    {Ω ι E : Type*} [MeasurableSpace Ω] [MeasurableSpace E] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ)
    (hX : Measurable X) {a : ℝ} (ha : a ≤ 1/2) (hx : ∀ w, |X w| ≤ a)
    (_hEX : (∫ w, X w ∂P)=0)
    (G : Ω → E) (hG : Measurable G) :
    iIndepFun (fun i (x : ι → Ω) ↦ G (x i))
      ((Measure.pi (fun _ : ι ↦ P)).tilted (fun x ↦ ∑ i, Real.log (1+X (x i)))) := by
  have hi : Integrable (fun w ↦ Real.exp (Real.log (1+X w))) P := by
    simp_rw [exp_logPerturbation_eq ha (hx _)]
    exact (integrable_const 1).add (integrable_of_uniform_abs P hX hx)
  rw [true_product_tilt_eq_general P _ hi]
  letI : IsProbabilityMeasure (P.tilted (fun w ↦ Real.log (1+X w))) :=
    isProbabilityMeasure_tilted hi
  exact iIndepFun_pi (fun _ ↦ hG.aemeasurable)

end CubeSqrtProbability
#print axioms CubeSqrtProbability.true_product_tilt_eq_general
#print axioms CubeSqrtProbability.true_winner_tilt_independent
