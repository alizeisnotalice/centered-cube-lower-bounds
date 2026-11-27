import MDWindow
import StandardizedLength
import ModerateNumeric
import NormalizedSaddle
import NormalTailTransfer
import TiltedBerryRow

open MeasureTheory ProbabilityTheory Set
set_option maxHeartbeats 500000
namespace CubeMD

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {X : Ω → ℝ}

noncomputable def mdLowerConstant : ℝ := gaussianPDFReal 0 1 3 / (2 * Real.sqrt 6 * Real.exp 1)
noncomputable def mdUpperConstant : ℝ := (3 * (Real.sqrt (2 * Real.pi))⁻¹ + 2) / (1 - Real.exp (-1))


/-- G4 for bounded iid rows on a product space. The threshold is conservatively
larger than the manuscript's; the tail and rate constants are unchanged. -/
theorem iid_moderate_deviation (n : ℕ) (hn : 0 < n)
    (hX : Measurable X) (b : ℝ) (hb0 : 0 ≤ b)
    (hb : ∀ᵐ x ∂μ, |X x| ≤ b)
    (hmean : (∫ x, X x ∂μ) = 0) (hvar : (∫ x, X x ^ 2 ∂μ) = 1)
    (hN0 : (32 * b ^ 3) ^ 3 ≤ (n : ℝ))
    (hN1 : (4 * Real.sqrt 6 * (30 * 64 * b ^ 3) / gaussianPDFReal 0 1 3) ^ 3 ≤ (n : ℝ))
    (hN2 : (30 * 64 * b ^ 3) ^ 3 ≤ (n : ℝ))
    (z : ℝ) (hz : 1 ≤ z) (hWin : z ^ 6 ≤ (n : ℝ)) :
    let P := Measure.pi (fun _ : Fin n ↦ μ)
    let r := Real.sqrt (n : ℝ)
    let T := {x : Fin n → Ω | z ≤ (∑ i, X (x i)) / r}
    mdLowerConstant / z * Real.exp (-(z ^ 2 / 2) - 72 * b ^ 3 * z ^ 3 / r) ≤ P.real T ∧
    P.real T ≤ mdUpperConstant / z * Real.exp (-(z ^ 2 / 2) + 72 * b ^ 3 * z ^ 3 / r) := by
  dsimp
  let P := Measure.pi (fun _ : Fin n ↦ μ)
  let S : (Fin n → Ω) → ℝ := fun x ↦ ∑ i, X (x i)
  let r := Real.sqrt (n : ℝ)
  let y := z / r
  let B := 30 * 64 * b ^ 3
  let δ := B / r
  let φ := gaussianPDFReal 0 1 3
  have hnr : 0 < (n : ℝ) := by exact_mod_cast hn
  have hr : 0 < r := Real.sqrt_pos.2 hnr
  have hz' : 0 < z := zero_lt_one.trans_le hz
  have hy : 0 < y := div_pos hz' hr
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hφ : 0 < φ := gaussianPDFReal_pos 0 1 3 (by norm_num)
  have h6 : 0 < Real.sqrt 6 := by positivity
  have h0 := window_root_le n z (32 * b ^ 3) hz'.le (by positivity) hWin hN0
  have hsmall : 8 * b ^ 3 * (2 * y) ≤ 1 / 2 := by
    have h : (32 * b ^ 3 * z) / r ≤ (1 : ℝ) :=
      (div_le_iff₀ hr).2 (by simpa only [one_mul] using h0)
    have heq : (32 * b ^ 3 * z) / r = 2 * (8 * b ^ 3 * (2 * y)) := by dsimp only [y]; ring
    rw [heq] at h
    linarith only [h]
  obtain ⟨q, hqL, hqU, hqmean, hqvar, hqrate⟩ :=
    normalized_saddle_with_rate b y hb0 hy hsmall hX.aemeasurable hb hmean hvar
  let v := iteratedDeriv 2 (cgf X μ) q
  let sd := r * Real.sqrt v
  have hv : 0 < v := lt_of_lt_of_le (by norm_num) hqvar.1
  have hsd : 0 < sd := mul_pos hr (Real.sqrt_pos.2 hv)
  have hq : 0 < q := lt_of_lt_of_le (by positivity) hqL
  have hyz : y * r = z := div_mul_cancel₀ _ hr.ne'
  have hLengths := standardized_strip_length q y r v hy hr hqL hqU hqvar
  rw [hyz] at hLengths
  have hE1 : 2 * δ ≤ φ / (2 * Real.sqrt 6 * z) := by
    have h := window_root_le n z (4 * Real.sqrt 6 * B / φ) hz'.le (by positivity) hWin hN1
    have h' := (div_le_iff₀ hφ).mp (show (4 * Real.sqrt 6 * B * z) / φ ≤ r by
      simpa [div_mul_eq_mul_div] using h)
    apply (le_div_iff₀ (mul_pos (mul_pos (by norm_num) h6) hz')).2
    calc
      _ = (4 * Real.sqrt 6 * B * z) / r := by dsimp only [δ]; ring
      _ ≤ φ := (div_le_iff₀ hr).2 (by simpa only [mul_comm r φ] using h')
  have hE2 : 2 * δ ≤ 2 / z := by
    have h := window_root_le n z B hz'.le hB hWin hN2
    apply (le_div_iff₀ hz').2
    calc
      _ = (2 * (B * z)) / r := by dsimp only [δ]; ring
      _ ≤ 2 := (div_le_iff₀ hr).2 (by linarith only [h])
  have hCDF := tilted_iid_normal_cdf (μ := μ) (X := X) (q := q) hn hX hb0 hb hqvar.1
  dsimp only at hCDF
  rw [hqmean] at hCDF
  have hExp : ∀ x : Fin n → Ω, Real.exp (q * S x) = ∏ i, Real.exp (q * X (x i)) := by
    intro x
    dsimp only [S]
    rw [Finset.mul_sum, Real.exp_sum]
  have ht : q ∈ interior (integrableExpSet X μ) := by
    rw [all_real_tilts hX.aemeasurable hb]
    exact Set.mem_univ _
  have he := integrable_of_mem_integrableExpSet (interior_subset ht)
  have hSE : Integrable (fun x ↦ Real.exp (q * S x)) P := by
    simp only [hExp, P]
    exact Integrable.fintype_prod (μ := fun _ : Fin n ↦ μ)
      (f := fun _ x ↦ Real.exp (q * X x)) (fun _ ↦ he)
  have hS : Measurable S := Finset.measurable_fun_sum _ fun i _ ↦ hX.comp (measurable_pi_apply i)
  have hTail := tilted_tail_of_normal_cdf (μ := P) (X := S) hS q (n * y) sd z δ hq hsd hz hSE
    hLengths.1 hLengths.2 hE1 hE2 hCDF
  have hcgf : cgf S P q = n * cgf X μ q := by
    simp only [cgf, mgf, hExp, P]
    rw [integral_fintype_prod_eq_pow (ι := Fin n) (μ := μ) (fun x ↦ Real.exp (q * X x)),
      Fintype.card_fin, Real.log_pow]
  let L := q * (n * y) - cgf S P q
  have hr2 : r ^ 2 = n := Real.sq_sqrt hnr.le
  have hRy2 : (n : ℝ) * (y ^ 2 / 2) = z ^ 2 / 2 := by
    dsimp only [y]
    rw [div_pow, hr2]
    field_simp [hnr.ne', hr.ne'] <;> ring
  have hRy3 : (n : ℝ) * (72 * b ^ 3 * y ^ 3) = 72 * b ^ 3 * z ^ 3 / r := by
    dsimp only [y]
    rw [div_pow, pow_succ r 2, hr2]
    field_simp [hnr.ne', hr.ne'] <;> ring
  have hRate : |L - z ^ 2 / 2| ≤ 72 * b ^ 3 * z ^ 3 / r := by
    rw [← hRy2, ← hRy3]
    have heq : L - n * (y ^ 2 / 2) = n * (q * y - cgf X μ q - y ^ 2 / 2) := by
      dsimp only [L]
      rw [hcgf]
      ring
    rw [heq, abs_mul, abs_of_pos hnr]
    exact mul_le_mul_of_nonneg_left hqrate hnr.le
  have ey : (n : ℝ) * y = z * r := calc
    _ = r ^ 2 * y := by rw [hr2]
    _ = (y * r) * r := by ring
    _ = _ := by rw [hyz]
  have hA : (S ⁻¹' Ici (n * y)) = {x | z ≤ S x / r} := by
    ext x
    change (n : ℝ) * y ≤ S x ↔ z ≤ S x / r
    rw [ey, le_div_iff₀ hr]
  let c := φ / (2 * Real.sqrt 6)
  let C := 3*(Real.sqrt (2*Real.pi))⁻¹ + 2
  have hc : 0 ≤ c := div_nonneg hφ.le (by positivity)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hconst : φ / (2*Real.sqrt 6*z) = c/z := by dsimp only [c]; ring
  rw [hconst] at hTail
  have hneg : -q * (n*y) + cgf S P q = -L := by dsimp only [L]; ring
  rw [hneg] at hTail
  have hfinish := finish_md_numeric (P.real (S ⁻¹' Ici (n*y))) z L
    (72*b^3*z^3/r) c C hz' hc hC hRate hTail.1 hTail.2
  rw [hA] at hfinish
  have hLower : c / Real.exp 1 = mdLowerConstant := by
    unfold mdLowerConstant
    dsimp only [c,φ]
    ring
  rw [hLower] at hfinish
  exact hfinish

end CubeMD
#print axioms CubeMD.iid_moderate_deviation
