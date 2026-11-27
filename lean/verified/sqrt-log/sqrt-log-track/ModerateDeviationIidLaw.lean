import ModerateDeviation
import IidLawTransfer

open MeasureTheory ProbabilityTheory Set
namespace CubeMD

/-- The product-space moderate-deviation theorem for independent real
random variables on an arbitrary common probability space. -/
theorem iid_moderate_deviation_of_law {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    [IsProbabilityMeasure ν] {n : ℕ} (hn : 0 < n) {X : Fin n → Ω → ℝ}
    (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X ν) {μ : Measure ℝ}
    [IsProbabilityMeasure μ] (hlaw : ∀ i, ν.map (X i) = μ)
    (b : ℝ) (hb0 : 0 ≤ b) (hb : ∀ᵐ x ∂μ, |x| ≤ b)
    (hmean : (∫ x, x ∂μ) = 0) (hvar : (∫ x, x ^ 2 ∂μ) = 1)
    (hN0 : (32 * b ^ 3) ^ 3 ≤ (n : ℝ))
    (hN1 : (4 * Real.sqrt 6 * (30 * 64 * b ^ 3) / gaussianPDFReal 0 1 3) ^ 3 ≤ (n : ℝ))
    (hN2 : (30 * 64 * b ^ 3) ^ 3 ≤ (n : ℝ))
    (z : ℝ) (hz : 1 ≤ z) (hWin : z ≤ (n : ℝ) ^ (1 / 6 : ℝ)) :
    let r := Real.sqrt (n : ℝ)
    let T := {w : Ω | z ≤ (∑ i, X i w) / r}
    mdLowerConstant / z * Real.exp (-(z ^ 2 / 2) - 72 * b ^ 3 * z ^ 3 / r) ≤ ν.real T ∧
    ν.real T ≤ mdUpperConstant / z * Real.exp (-(z ^ 2 / 2) + 72 * b ^ 3 * z ^ 3 / r) := by
  dsimp only
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hz' : 0 ≤ z := by linarith
  have hWin' : z ^ 6 ≤ (n : ℝ) := by
    have hh : z ≤ (n : ℝ) ^ (6 : ℝ)⁻¹ := by simpa only [one_div] using hWin
    have hh' := (Real.le_rpow_inv_iff_of_pos hz' hn'.le (by norm_num : (0 : ℝ) < 6)).mp hh
    rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at hh'
    exact hh'
  have hp := iid_moderate_deviation (μ := μ) (X := id) n hn measurable_id b hb0 hb hmean hvar
    hN0 hN1 hN2 z hz hWin'
  dsimp only [id_eq] at hp
  let r := Real.sqrt (n : ℝ)
  have hr : 0 < r := Real.sqrt_pos.mpr hn'
  have hs (f : Ω → ℝ) : {w : Ω | z ≤ f w / r} = {w : Ω | z * r ≤ f w} := by
    ext w
    exact le_div_iff₀ hr
  have hs' (f : (Fin n → ℝ) → ℝ) :
      {w : Fin n → ℝ | z ≤ f w / r} = {w : Fin n → ℝ | z * r ≤ f w} := by
    ext w
    exact le_div_iff₀ hr
  change _ ≤ ν.real {w : Ω | z ≤ (∑ i, X i w) / r} ∧
    ν.real {w : Ω | z ≤ (∑ i, X i w) / r} ≤ _
  rw [hs (fun w ↦ ∑ i, X i w), iid_sum_tail_eq_product hX hind hlaw (z * r)]
  change _ ≤ (Measure.pi (fun _ : Fin n ↦ μ)).real {w | z ≤ (∑ i, w i) / r} ∧
    (Measure.pi (fun _ : Fin n ↦ μ)).real {w | z ≤ (∑ i, w i) / r} ≤ _ at hp
  rw [hs' (fun w ↦ ∑ i, w i)] at hp
  exact hp

end CubeMD
#print axioms CubeMD.iid_moderate_deviation_of_law
