import Kernel
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

open Finset

namespace CenteredCube.RudinDensity

private theorem cosine_step_bounds {τ y : ℝ} (hτ : |τ| ≤ 1/8)
    (hy : 1 ≤ y) (hy' : y ≤ 2) :
    8 * τ^2 ≤ 1 - Real.cos (2 * Real.pi * τ * y) ∧
      1 - Real.cos (2 * Real.pi * τ * y) ≤ 8 * Real.pi^2 * τ^2 := by
  let z : ℝ := Real.pi * |τ| * y
  have hp := Real.pi_pos
  have hy0 : 0 ≤ y := by linarith
  have hτ0 := abs_nonneg τ
  have hz0 : 0 ≤ z := by dsimp [z]; positivity
  have ht₁ : |τ| * y ≤ 1/4 := by
    calc
      |τ| * y ≤ (1/8) * y := mul_le_mul_of_nonneg_right hτ hy0
      _ ≤ 1/4 := by linarith
  have hz₁ : z ≤ Real.pi/2 := by
    dsimp [z]
    nlinarith only [mul_le_mul_of_nonneg_left ht₁ hp.le, hp]
  have hsinL := Real.mul_le_sin hz0 hz₁
  have hsinR : Real.sin z ≤ z := by
    exact (le_abs_self _).trans ((Real.abs_sin_le_abs (x := z)).trans_eq (abs_of_nonneg hz0))
  have hcoef : 2 / Real.pi * z = 2 * (|τ| * y) := by
    dsimp [z]
    field_simp
  rw [hcoef] at hsinL
  have hsmall : 2 * |τ| ≤ Real.sin z := by
    have hh : |τ| * 1 ≤ |τ| * y := mul_le_mul_of_nonneg_left hy hτ0
    linarith
  have hlarge : Real.sin z ≤ 2 * Real.pi * |τ| := by
    apply hsinR.trans
    have hh := mul_le_mul_of_nonneg_left hy' (show 0 ≤ Real.pi * |τ| by positivity)
    dsimp [z]
    nlinarith only [hh]
  have hs0 : 0 ≤ Real.sin z := (by positivity : 0 ≤ 2 * |τ|).trans hsmall
  have hL : (2 * |τ|)^2 ≤ (Real.sin z)^2 := by gcongr
  have hR : (Real.sin z)^2 ≤ (2 * Real.pi * |τ|)^2 := by gcongr
  have hc : Real.cos (2 * Real.pi * τ * y) = Real.cos (2 * z) := by
    conv_lhs => rw [← Real.cos_abs]
    congr 1
    simp only [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * Real.pi), abs_of_nonneg hy0]
    dsimp [z]
    ring
  rw [hc, Real.cos_two_mul]
  have hide : Real.cos z ^ 2 + Real.sin z ^ 2 = 1 := by linarith [Real.sin_sq_add_cos_sq z]
  rw [mul_pow, sq_abs] at hL
  rw [mul_pow, sq_abs] at hR
  constructor <;> nlinarith only [hide, hL, hR]

theorem dirichlet_quadratic {K : ℕ} (hK : 0 < K) {τ : ℝ}
    (hτ : |τ| ≤ 1/8) :
    8 * τ^2 ≤ 1 - ReDK K τ ∧
      1 - ReDK K τ ≤ 8 * Real.pi^2 * τ^2 := by
  let F : ℕ → ℝ := fun l => 1 - Real.cos (2 * Real.pi * τ * (1 + (l:ℝ) / (K:ℝ)))
  have hK' : (0 : ℝ) < (K:ℝ) := by exact_mod_cast hK
  have hsum : 1 - ReDK K τ = (1 / (K:ℝ)) * ∑ l ∈ range K, F l := by
    rw [ReDK_eq]
    dsimp [F]
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp
  have term : ∀ l ∈ range K, 8 * τ^2 ≤ F l ∧ F l ≤ 8 * Real.pi^2 * τ^2 := by
    intro l hl
    have hcast : (l : ℝ) < (K : ℝ) := by exact_mod_cast mem_range.mp hl
    have hh : (l:ℝ) / (K:ℝ) ≤ 1 := (div_le_one hK').2 hcast.le
    exact cosine_step_bounds hτ (le_add_of_nonneg_right (by positivity)) (by linarith)
  have hl : (K:ℝ) * (8 * τ^2) ≤ ∑ l ∈ range K, F l := by
    simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using
      (Finset.sum_le_sum (fun l hl => (term l hl).1) :
        (∑ _l ∈ range K, 8 * τ^2) ≤ ∑ l ∈ range K, F l)
  have hr : (∑ l ∈ range K, F l) ≤ (K:ℝ) * (8 * Real.pi^2 * τ^2) := by
    simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using
      (Finset.sum_le_sum (fun l hl => (term l hl).2) :
        (∑ l ∈ range K, F l) ≤ ∑ _l ∈ range K, 8 * Real.pi^2 * τ^2)
  rw [hsum, one_div_mul_eq_div]
  exact ⟨(le_div_iff₀ hK').2 (by simpa [mul_comm] using hl),
    (div_le_iff₀ hK').2 (by simpa [mul_comm] using hr)⟩

theorem covariance_quadratic {K : ℕ} (hK : 4 ≤ K) {u a t s : ℝ}
    (hu : 3/50 ≤ u) (ha : 0 < a)
    (ht : |t - (K : ℝ) / 4| ≤ (K : ℝ) / (100 * u))
    (hs : |s - (K : ℝ) / 4| ≤ (K : ℝ) / (100 * u))
    (hlo : a/u ≤ |t-s|) (hhi : |t-s| ≤ 1/8)
    (hscale : 2*u^2/a^2 ≤ (K:ℝ)) :
    4 * |t-s|^2 ≤ 1 - kappa K t s ∧
      1 - kappa K t s ≤ (8 * Real.pi^2 + 4) * |t-s|^2 := by
  have hK' : (0:ℝ) < (K:ℝ) := by exact_mod_cast (show 0 < K by omega)
  have hu0 : 0 < u := by linarith
  have habs : 0 ≤ |t-s| := abs_nonneg _
  have hzero : 0 ≤ a/u := by positivity
  have hstay : (a/u)^2 ≤ |t-s|^2 := by gcongr
  have hgap : 8 / (K:ℝ) ≤ 4 * |t-s|^2 := by
    apply le_trans _ (mul_le_mul_of_nonneg_left hstay (by norm_num : (0:ℝ) ≤ 4))
    apply (div_le_iff₀ hK').2
    have hval : 2 * u^2 ≤ (K:ℝ) * a^2 := (div_le_iff₀ (by positivity : 0 < a^2)).1 hscale
    rw [div_pow]
    have he : 4 * (a^2/u^2) * (K:ℝ) = (4 * (K:ℝ) * a^2) / u^2 := by ring
    rw [he]
    exact (le_div_iff₀ (by positivity : 0 < u^2)).2 (by linarith)
  have H := dirichlet_quadratic (show 0 < K by omega) hhi
  have E := abs_le.mp (finite_kernel hK hu ht hs)
  rw [sq_abs]
  rw [sq_abs] at hgap
  constructor <;> nlinarith only [H.1, H.2, E.1, E.2, hgap]

end CenteredCube.RudinDensity

#print axioms CenteredCube.RudinDensity.dirichlet_quadratic
#print axioms CenteredCube.RudinDensity.covariance_quadratic
