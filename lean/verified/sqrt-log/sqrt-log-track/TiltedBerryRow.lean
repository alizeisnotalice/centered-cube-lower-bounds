import ProductTilt
import TiltedMoments
import BerryClosedCDF

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
set_option maxHeartbeats 1500000
namespace CubeMD

private theorem sum_third_budget (n r v b : ℝ)
    (hnv : 0 < n) (hr : 0 < r) (hr2 : r ^ 2 = n)
    (hv : 1 / 2 ≤ v) (hb0 : 0 ≤ b) :
    30 * (n * (8 * b ^ 3 / (r * Real.sqrt v) ^ 3)) ≤ 30 * 64 * b ^ 3 / r := by
  let sd := r * Real.sqrt v
  change 30 * (n * (8 * b ^ 3 / sd ^ 3)) ≤ _
  have hv0 : 0 < v := lt_of_lt_of_le (by norm_num) hv
  have hs : 0 < Real.sqrt v := Real.sqrt_pos.2 hv0
  have hhalf : (1 / 2 : ℝ) ≤ Real.sqrt v := by
    apply le_of_sq_le_sq _ hs.le
    rw [Real.sq_sqrt hv0.le]
    linarith [show (1 / 2 : ℝ) ^ 2 ≤ 1 / 2 by norm_num]
  have hcube : r ^ 3 / 8 ≤ sd ^ 3 := by
    calc
      _ = (r * (1 / 2)) ^ 3 := by ring
      _ ≤ _ := pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hhalf hr.le) _
  have hsimp : r ^ 3 = n * r := by rw [pow_succ, hr2]
  calc
    _ ≤ 30 * (n * (8 * b ^ 3 / (r ^ 3 / 8))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_left (by positivity) (by positivity) hcube) hnv.le) (by norm_num)
    _ = _ := by rw [hsimp]; field_simp [hnv.ne', hr.ne']; ring

theorem tilted_iid_normal_cdf {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} {n : ℕ} (hn : 0 < n)
    (hX : Measurable X) {b q : ℝ} (hb0 : 0 ≤ b)
    (hb : ∀ᵐ x ∂μ, |X x| ≤ b)
    (hv : 1 / 2 ≤ iteratedDeriv 2 (cgf X μ) q) :
    let S : (Fin n → Ω) → ℝ := fun x ↦ ∑ i, X (x i)
    let m := deriv (cgf X μ) q
    let sd := Real.sqrt (n : ℝ) * Real.sqrt (iteratedDeriv 2 (cgf X μ) q)
    ∀ a : ℝ, |(((Measure.pi (fun _ : Fin n ↦ μ)).tilted (q * S ·)).map
        (fun x ↦ (S x - n * m) / sd)).real (Iic a)
      - (gaussianReal 0 1).real (Iic a)| ≤ 30 * 64 * b ^ 3 / Real.sqrt (n : ℝ) := by
  dsimp only
  let ν := μ.tilted (q * X ·)
  let m := deriv (cgf X μ) q
  let v := iteratedDeriv 2 (cgf X μ) q
  let r := Real.sqrt (n : ℝ)
  let sd := r * Real.sqrt v
  let Y : Ω → ℝ := fun x ↦ (X x - m) / sd
  let νπ := Measure.pi (fun _ : Fin n ↦ ν)
  let Z : Fin n → (Fin n → Ω) → ℝ := fun i x ↦ Y (x i)
  have hnv : 0 < (n : ℝ) := by exact_mod_cast hn
  have hr : 0 < r := Real.sqrt_pos.2 hnv
  have hv0 : 0 < v := lt_of_lt_of_le (by norm_num) hv
  have hs : 0 < Real.sqrt v := Real.sqrt_pos.2 hv0
  have hsd : 0 < sd := mul_pos hr hs
  have ht : q ∈ interior (integrableExpSet X μ) := by
    rw [all_real_tilts hX.aemeasurable hb]
    exact Set.mem_univ _
  have he := integrable_of_mem_integrableExpSet (interior_subset ht)
  haveI : IsProbabilityMeasure ν := isProbabilityMeasure_tilted he
  letI : ∀ _i : Fin n, IsProbabilityMeasure ν := fun _ ↦ inferInstance
  haveI : IsProbabilityMeasure νπ := by dsimp only [νπ]; infer_instance
  have hY : Measurable Y := (hX.sub_const m).div_const sd
  have h_eval (i : Fin n) : MeasurePreserving (fun x : Fin n → Ω ↦ x i) νπ ν :=
    measurePreserving_eval (fun _ : Fin n ↦ ν) i
  have hZ (i : Fin n) : Measurable (Z i) := hY.comp (h_eval i).measurable
  have hZind : iIndepFun Z νπ := iIndepFun_pi (fun _i : Fin n ↦ hY.aemeasurable)
  have hMean : ∫ x, X x ∂ν = m := integral_tilted_mul_self ht
  have hVar : variance X ν = v := variance_tilted_mul ht
  have hX2 : MemLp X 2 ν := memLp_tilted_mul ht 2
  have hY2 : MemLp Y 2 ν := by
    simp only [Y, div_eq_inv_mul]
    exact (hX2.sub (memLp_const m)).const_smul sd⁻¹
  have hZ2 (i : Fin n) : MemLp (Z i) 2 νπ := hY2.comp_measurePreserving (h_eval i)
  have hYmean : ∫ x, Y x ∂ν = 0 := by
    simp only [Y]
    rw [integral_div, integral_sub (hX2.integrable (by norm_num)) (integrable_const _), hMean]
    simp
  have hZmean (i : Fin n) : ∫ x, Z i x ∂νπ = 0 := by
    rw [show (∫ x, Z i x ∂νπ) = ∫ x, Y x ∂ν from
      integral_comp_eval (μ := fun _ : Fin n ↦ ν) (i := i) (f := Y) hY.aestronglyMeasurable]
    exact hYmean
  have hsquare : sd ^ 2 = (n : ℝ) * v := by
    rw [show sd = r * Real.sqrt v from rfl, mul_pow, Real.sq_sqrt hv0.le, Real.sq_sqrt hnv.le]
  have hYvar : variance Y ν = (n : ℝ)⁻¹ := by
    simp only [Y, div_eq_inv_mul]
    rw [variance_const_mul, variance_sub_const hX.aestronglyMeasurable, hVar, inv_pow, hsquare]
    field_simp [hnv.ne', hv0.ne']
  have hZvar (i : Fin n) : variance (Z i) νπ = (n : ℝ)⁻¹ := by
    rw [show variance (Z i) νπ = variance Y ν from (h_eval i).variance_fun_comp hY.aemeasurable, hYvar]
  have hTotal : ∑ i, variance (Z i) νπ = 1 := by simp [hZvar, hnv.ne']
  have hY3 : Integrable (fun x ↦ |Y x| ^ 3) ν := by
    have hX3 : MemLp X (3 : ℝ≥0∞) ν := memLp_tilted_mul ht 3
    have hY3' : MemLp Y (3 : ℝ≥0∞) ν := by
      simp only [Y, div_eq_inv_mul]
      exact (hX3.sub (memLp_const m)).const_smul sd⁻¹
    simpa [Real.norm_eq_abs] using hY3'.integrable_norm_pow'
  have hZ3 (i : Fin n) : Integrable (fun x ↦ |Z i x| ^ 3) νπ :=
    (h_eval i).integrable_comp_of_integrable hY3
  have h3Y : (∫ w, |Y w| ^ 3 ∂ν) ≤ 8 * b ^ 3 / sd ^ 3 := by
    simp only [Y, abs_div, abs_of_pos hsd, div_pow, integral_div]
    exact div_le_div_of_nonneg_right (tilted_third_abs_moment hX.aemeasurable hb0 hb q) (by positivity)
  have h3Z (i : Fin n) : (∫ w, |Z i w| ^ 3 ∂νπ) ≤ 8 * b ^ 3 / sd ^ 3 := by
    have hmeas : Measurable (fun w ↦ |Y w| ^ 3) := (continuous_abs.measurable.comp hY).pow_const _
    exact (le_of_eq (integral_comp_eval (μ := fun _ : Fin n ↦ ν)
      (i := i) (f := fun w ↦ |Y w| ^ 3) hmeas.aestronglyMeasurable)).trans h3Y
  have hBE := fin_row_berry_closed_cdf hZ hZ2 hZind hZmean hTotal hZ3 _ h3Z
  have hnorm : (fun x : Fin n → Ω ↦ (∑ i, X (x i) - n * m) / sd) =
      (fun x ↦ ∑ i, Z i x) := by
    funext x
    change (∑ i, X (x i) - (n : ℝ) * m) / sd = ∑ i, (X (x i) - m) / sd
    rw [← Finset.sum_div, Finset.sum_sub_distrib]
    simp
  intro a
  change |(((Measure.pi (fun _ : Fin n ↦ μ)).tilted
      (fun x : Fin n → Ω ↦ q * ∑ i, X (x i))).map
      (fun x ↦ (∑ i, X (x i) - n * m) / sd)).real (Iic a)
      - (gaussianReal 0 1).real (Iic a)| ≤ _
  rw [tilted_pi_eq_pi_tilted (fun _ : Fin n ↦ μ) (fun _ ↦ X) q (fun _ ↦ he), hnorm]
  apply (hBE a).trans
  exact sum_third_budget n r v b hnv hr (Real.sq_sqrt hnv.le) hv hb0

end CubeMD
#print axioms CubeMD.tilted_iid_normal_cdf
