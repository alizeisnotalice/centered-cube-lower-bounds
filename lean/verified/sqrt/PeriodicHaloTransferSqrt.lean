import SqrtCellMeasure
import SharpTruncationTransfer
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Pi

open MeasureTheory Set
open scoped ENNReal Interval BigOperators

namespace CenteredCube

noncomputable def productSource {n : ℕ} (ρ : ℝ → ℝ) (x : Space n) : ℝ :=
  ∏ i, ρ (x i)

noncomputable def intervalSource (ρ : ℝ → ℝ) (r x : ℝ) : ℝ :=
  (1/r)*(∫ y in (x-r/2)..(x+r/2), ρ y)

theorem cube_as_product_Icc {n : ℕ} (x : Space n) (r : ℝ) :
    cube x r = Set.univ.pi (fun i => Icc (x i-r/2) (x i+r/2)) := by
  ext y
  simp only [cube, Set.mem_Icc, Set.mem_pi, Set.mem_univ, forall_true_left]
  exact ⟨fun ⟨hl,hu⟩ i => ⟨hl i,hu i⟩, fun h => ⟨fun i => (h i).1, fun i => (h i).2⟩⟩

theorem productSource_integrableOn_box {n : ℕ} (ρ : ℝ → ℝ)
    (hρ : ∀ a b, IntervalIntegrable ρ volume a b)
    (a b : Space n) (hab : a ≤ b) :
    IntegrableOn (productSource ρ) (Icc a b) volume := by
  have he : Icc a b = univ.pi (fun i => Icc (a i) (b i)) := by
    ext y
    simp only [Set.mem_Icc, Set.mem_pi, Set.mem_univ, forall_true_left]
    exact ⟨fun ⟨hl,hu⟩ i => ⟨hl i,hu i⟩, fun h => ⟨fun i => (h i).1, fun i => (h i).2⟩⟩
  unfold IntegrableOn productSource
  rw [he, volume_pi, Measure.restrict_pi_pi]
  apply Integrable.fintype_prod
  intro i
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le (hab i)).1 (hρ _ _)

theorem cubeAverage_of_productSource {n : ℕ} (ρ : ℝ → ℝ) (hpos : ∀ x, 0 ≤ ρ x)
    (hρ : ∀ a b, IntervalIntegrable ρ volume a b) (x : Space n) {r : ℝ}
    (hr : 0 < r) :
    cubeAverage (productSource ρ) x r = ENNReal.ofReal (∏ i, intervalSource ρ r (x i)) := by
  have hInt : IntegrableOn (productSource ρ) (cube x r) volume :=
    productSource_integrableOn_box ρ hρ _ _ (fun i => by linarith)
  have hNN0 : ∀ y : Space n, 0 ≤ productSource ρ y :=
    fun y => Finset.prod_nonneg (fun i _ => hpos (y i))
  have hNN : 0 ≤ᵐ[volume.restrict (cube x r)] productSource ρ :=
    Filter.Eventually.of_forall hNN0
  unfold cubeAverage
  simp_rw [abs_of_nonneg (hNN0 _)]
  rw [← ofReal_integral_eq_lintegral_ofReal hInt hNN,
    ← ENNReal.ofReal_pow hr.le, ← ENNReal.ofReal_div_of_pos (pow_pos hr _),
    cube_as_product_Icc]
  unfold productSource
  rw [show (volume : Measure (Space n)) = Measure.pi (fun _ : Fin n ↦ volume) from volume_pi,
    Measure.restrict_pi_pi, integral_fintype_prod_eq_prod]
  have hi (i : Fin n) :
      (∫ y in Icc (x i-r/2) (x i+r/2), ρ y) =
        ∫ y in (x i-r/2)..(x i+r/2), ρ y := by
    rw [intervalIntegral.integral_of_le (by linarith : x i-r/2 ≤ x i+r/2),
      integral_Icc_eq_integral_Ioc]
  simp_rw [hi]
  congr 1
  unfold intervalSource
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, one_div,
    inv_pow, div_eq_mul_inv, mul_comm]

theorem truncation_mass_of_periodic_product {n : ℕ} (ρ : ℝ → ℝ)
    (hpos : ∀ x, 0 ≤ ρ x) (hρ : ∀ a b, IntervalIntegrable ρ volume a b)
    (hper : Function.Periodic ρ 1) (hm : (∫ x in (0:ℝ)..1, ρ x) = 1) (R : ℕ) :
    absMass ((box n R).indicator (productSource ρ)) = ENNReal.ofReal ((2*(R:ℝ))^n) := by
  have hI : IntegrableOn (productSource ρ) (box n (R:ℝ)) volume :=
    productSource_integrableOn_box ρ hρ _ _ (fun _ => neg_le_self (Nat.cast_nonneg R))
  have hNN : 0 ≤ᵐ[volume.restrict (box n (R:ℝ))] productSource ρ :=
    Filter.Eventually.of_forall (fun y => Finset.prod_nonneg (fun i _ => hpos (y i)))
  have hbox : box n (R:ℝ) = univ.pi (fun _ : Fin n => Icc (-(R:ℝ)) (R:ℝ)) := sqrt_box_eq_pi
  have hmass1 : (∫ x in Icc (-(R:ℝ)) (R:ℝ), ρ x) = 2 * (R:ℝ) := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (neg_le_self (Nat.cast_nonneg R) : -(R:ℝ) ≤ R)]
    have h := hper.intervalIntegral_add_zsmul_eq (2*(R:ℤ)) (-(R:ℝ)) hρ
    have hshift : -(R:ℝ) + (2*(R:ℤ)) • (1:ℝ) = R := by simp [zsmul_eq_mul]; ring
    rw [hshift] at h
    rw [h, hper.intervalIntegral_add_eq (-(R:ℝ)) 0]
    simp [hm, zsmul_eq_mul]
  unfold absMass
  have hi : (fun x => ENNReal.ofReal |(box n (R:ℝ)).indicator (productSource ρ) x|) =
      (box n (R:ℝ)).indicator (fun x => ENNReal.ofReal (productSource ρ x)) := by
    funext x
    by_cases hx : x ∈ box n (R:ℝ)
    · have hn : 0 ≤ productSource ρ x := Finset.prod_nonneg (fun i _ => hpos (x i))
      rw [indicator_of_mem hx, indicator_of_mem hx, abs_of_nonneg hn]
    · simp [hx]
  have hb : MeasurableSet (box n (R:ℝ)) := isClosed_Icc.measurableSet
  rw [hi, lintegral_indicator hb, ← ofReal_integral_eq_lintegral_ofReal hI hNN,
    hbox]
  unfold productSource
  rw [volume_pi, Measure.restrict_pi_pi, integral_fintype_prod_eq_prod]
  simp [hmass1]

theorem intervalSource_periodic_int (ρ : ℝ → ℝ) (hper : Function.Periodic ρ 1)
    (r x : ℝ) (k : ℤ) : intervalSource ρ r (x+(k:ℝ)) = intervalSource ρ r x := by
  have hp (y : ℝ) : ρ (y+(k:ℝ)) = ρ y := by
    simpa [zsmul_eq_mul] using (hper.zsmul k) y
  unfold intervalSource
  rw [show x+(k:ℝ)-r/2 = (x-r/2)+(k:ℝ) by ring,
    show x+(k:ℝ)+r/2 = (x+r/2)+(k:ℝ) by ring,
    ← intervalIntegral.integral_comp_add_right]
  simp_rw [hp]

noncomputable def periodicLogScore {n : ℕ} (ρ : ℝ → ℝ) (r : ℝ) (x : Space n) : ℝ :=
  ∑ i, Real.log (intervalSource ρ r (x i))

theorem exp_periodicLogScore {n : ℕ} (ρ : ℝ → ℝ) (r : ℝ) (x : Space n)
    (hp : ∀ y, 0 < intervalSource ρ r y) :
    Real.exp (periodicLogScore ρ r x) = ∏ i, intervalSource ρ r (x i) := by
  unfold periodicLogScore
  rw [Real.exp_sum]
  exact Finset.prod_congr rfl (fun i _ => Real.exp_log (hp (x i)))

/-- From a genuine periodic product log-score event under the dimension-n product of
uniform cell laws, produce a compactly supported witness for the actual centered
maximal operator, with the exact asymptotically lossless retention factor. -/
theorem weakConstant_ge_periodic_log_event {n : ℕ} (hn : 1 ≤ n)
    (ρ : ℝ → ℝ) (hpos : ∀ x, 0 ≤ ρ x)
    (hρ : ∀ a b, IntervalIntegrable ρ volume a b)
    (hper : Function.Periodic ρ 1) (hm : (∫ x in (0:ℝ)..1, ρ x) = 1)
    (h : ℝ) (E : Set (Space n)) (hE : MeasurableSet E)
    (hwitness : ∀ x ∈ E, ∃ r : ℝ, 0 < r ∧ r ≤ 2 ∧
      (∀ y, 0 < intervalSource ρ r y) ∧ h < periodicLogScore ρ r x) :
    ENNReal.ofReal (Real.exp h * (sqrtCellLaw n).real E * (1-1/(n:ℝ)^2)^n)
      ≤ weakConstant n := by
  let R := n^2-1
  have hN : 1 ≤ n^2 := by nlinarith
  have hR : (R:ℝ) = (n:ℝ)^2-1 := by
    dsimp [R]
    rw [Nat.cast_sub hN, Nat.cast_pow, Nat.cast_one]
  let A := box n ((n:ℝ)^2-1) ∩ cellRep ⁻¹' E
  have hbox : MeasurableSet (box n ((n:ℝ)^2)) := isClosed_Icc.measurableSet
  have hIn : IntegrableOn (productSource ρ) (box n ((n:ℝ)^2)) volume :=
    productSource_integrableOn_box ρ hρ _ _ (fun _ => neg_le_self (sq_nonneg _))
  have hMass := truncation_mass_of_periodic_product (n := n) ρ hpos hρ hper hm (n^2)
  refine sharp_transfer_of_truncated_halo hn (productSource ρ) A
    (hIn.integrable_indicator hbox) (by simpa only [Nat.cast_pow] using hMass) ?_ ?_
  · change ENNReal.ofReal ((sqrtCellLaw n).real E * (2*(n:ℝ)^2-2)^n) ≤ volume A
    have hlen : 2*(n:ℝ)^2-2 = 2*(R:ℝ) := by rw [hR]; ring
    rw [hlen, mul_comm, ENNReal.ofReal_mul (by positivity)]
    simp only [Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _)]
    dsimp [A]
    rw [← hR, box_event_volume R E hE]
  · intro x hx
    obtain ⟨r,hr,hr2,hp,hlt⟩ := hwitness (cellRep x) hx.2
    refine ⟨hx.1,r,hr,hr2,?_⟩
    have hs (i : Fin n) : intervalSource ρ r (x i) = intervalSource ρ r (cellRep x i) := by
      have hc : cellRep x i + (ceilIndex x i:ℝ) = x i := by
        simp only [cellRep, cellShift, Pi.sub_apply]
        ring
      rw [← hc]
      exact intervalSource_periodic_int ρ hper r _ _
    rw [cubeAverage_of_productSource ρ hpos hρ x hr]
    have he := Real.exp_lt_exp.mpr hlt
    rw [exp_periodicLogScore ρ r (cellRep x) hp] at he
    have hprod : (∏ i, intervalSource ρ r (x i)) =
        ∏ i, intervalSource ρ r (cellRep x i) :=
      Finset.prod_congr rfl (fun i _ => hs i)
    rw [hprod]
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (Real.exp_pos _).le).2 he

#print axioms weakConstant_ge_periodic_log_event

#print axioms cubeAverage_of_productSource
#print axioms truncation_mass_of_periodic_product
#print axioms intervalSource_periodic_int

end CenteredCube
