/-
The window estimates `eq:window-bounds` of the manuscript.

For `K ≥ 4`, `u ≥ 3/50` and `|t − t₀| ≤ K/(100u)` with `t₀ = K/4`, the manuscript
claims

  `7/6 ≤ r(t) ≤ 11/6`,   `|V_K(t) − K/4| ≤ 1/2`,   `K/8 ≤ V_K(t) ≤ 3K/8`.

The variance bounds come from

  `V_K(t) = K/4 − ¼ Re ∑_{l<K} e^{4πit(1+l/K)}`,

`sin² v = (1 − cos 2v)/2`, together with the finite geometric sum

  `|∑_{l<K} e^{4πit(1+l/K)}| = |sin(2πt)|/|sin(2πt/K)| ≤ 2`,

the last inequality using `|sin(2πt/K)| = |cos(2π(t−t₀)/K)| ≥ 1/2` on the window
(since `|2π(t−t₀)/K| ≤ π/(50u) ≤ π/3`).

Together with `abs_Sfun_le` this yields the unconditional window form
`‖Y_t‖_∞ ≤ 5√8` (`abs_Y_le_window`), i.e. the conclusion of `lem:bounded`.
-/
import Dirichlet

open Finset Complex
open scoped BigOperators

namespace CenteredCube
namespace RudinDensity

/-- `V_K(t) = K/4 − ¼ ∑_{l<K} cos(4πt(1+l/K))`, from `sin²v = (1 − cos 2v)/2`. -/
theorem VK_eq_center_sub (K : ℕ) (t : ℝ) :
    VK K t = (K : ℝ) / 4
      - 1 / 4 * ∑ l ∈ range K, Real.cos (4 * Real.pi * t * (1 + (l : ℝ) / (K : ℝ))) := by
  have hterm : ∀ l ∈ range K,
      (1 / 2 : ℝ) * (Real.sin (2 * Real.pi * t * (1 + (l : ℝ) / (K : ℝ)))) ^ 2
        = 1 / 4 - 1 / 4 * Real.cos (4 * Real.pi * t * (1 + (l : ℝ) / (K : ℝ))) := by
    intro l _
    rw [Real.sin_sq_eq_half_sub]
    have h2 : 2 * (2 * Real.pi * t * (1 + (l : ℝ) / (K : ℝ)))
        = 4 * Real.pi * t * (1 + (l : ℝ) / (K : ℝ)) := by ring
    rw [h2]
    ring
  rw [VK, Finset.mul_sum, Finset.sum_congr rfl hterm, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← Finset.mul_sum]
  ring

/-- On the window: `7/6 ≤ r(t) ≤ 11/6`. -/
theorem rfun_window {K : ℕ} (hK : 1 ≤ K) {u t : ℝ} (hu : 3 / 50 ≤ u)
    (ht : |t - (K : ℝ) / 4| ≤ (K : ℝ) / (100 * u)) :
    7 / 6 ≤ rfun K t ∧ rfun K t ≤ 11 / 6 := by
  have hK0 : (0 : ℝ) < (K : ℝ) := by exact_mod_cast (by omega : 0 < K)
  have hupos : 0 < u := by linarith
  have h190 : 100 * u ≠ 0 := by positivity
  have hrt : rfun K t - 3 / 2 = 2 * (t - (K : ℝ) / 4) / (K : ℝ) := by
    unfold rfun
    field_simp
    ring
  have hbound : |rfun K t - 3 / 2| ≤ 1 / 3 := by
    rw [hrt, abs_div, abs_mul,
      abs_of_pos (by norm_num : (0:ℝ) < 2), abs_of_pos hK0]
    have h1 : 2 * |t - (K : ℝ) / 4| ≤ 2 * ((K : ℝ) / (100 * u)) := by
      have := mul_le_mul_of_nonneg_left ht (by norm_num : (0:ℝ) ≤ 2)
      linarith
    have h2 : 2 * ((K : ℝ) / (100 * u)) / (K : ℝ) = 1 / (50 * u) := by
      field_simp
      ring
    have h3 : 1 / (50 * u) ≤ 1 / 3 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    calc 2 * |t - (K : ℝ) / 4| / (K : ℝ)
        ≤ 2 * ((K : ℝ) / (100 * u)) / (K : ℝ) := by
          apply div_le_div_of_nonneg_right _ hK0.le
          linarith
      _ = 1 / (50 * u) := h2
      _ ≤ 1 / 3 := h3
  constructor <;> linarith [abs_le.mp hbound |>.1, abs_le.mp hbound |>.2]


/-- The exponential sum of the window estimates: `∑_{l<K} e^{4πit(1+l/K)}`. -/
noncomputable def Dsum (K : ℕ) (t : ℝ) : ℂ :=
  ∑ l ∈ range K, Complex.exp (((4 * Real.pi * t * (1 + (l : ℝ) / (K : ℝ)) : ℝ) : ℂ) * Complex.I)

/-- `Re Dsum = ∑ cos(4πt(1+l/K))`. -/
theorem Dsum_re (K : ℕ) (t : ℝ) :
    (Dsum K t).re = ∑ l ∈ range K,
      Real.cos (4 * Real.pi * t * (1 + (l : ℝ) / (K : ℝ))) := by
  unfold Dsum
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [Complex.exp_ofReal_mul_I]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_one,
    mul_zero, add_zero, zero_add, sub_zero]

/-- Geometric factorisation: `Dsum K t = e^{4πit} · ∑_{l<K} ζ^l` with `ζ = e^{4πit/K}`. -/
theorem Dsum_factor (K : ℕ) (t : ℝ) :
    Dsum K t = Complex.exp (((4 * Real.pi * t : ℝ) : ℂ) * Complex.I)
        * ∑ l ∈ range K,
          (Complex.exp (((4 * Real.pi * t / (K : ℝ) : ℝ) : ℂ) * Complex.I)) ^ l := by
  unfold Dsum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  have harg : (4 * Real.pi * t * (1 + (l : ℝ) / (K : ℝ)) : ℝ)
      = 4 * Real.pi * t + l * (4 * Real.pi * t / (K : ℝ)) := by
    field_simp
  rw [show ((4 * Real.pi * t * (1 + (l : ℝ) / (K : ℝ)) : ℝ) : ℂ) * Complex.I
      = ((4 * Real.pi * t + l * (4 * Real.pi * t / (K : ℝ)) : ℝ) : ℂ) * Complex.I by rw [harg],
    Complex.ofReal_add, add_mul, Complex.exp_add]
  rw [show ((l * (4 * Real.pi * t / (K : ℝ)) : ℝ) : ℂ) * Complex.I
      = ((l : ℂ)) * (((4 * Real.pi * t / (K : ℝ) : ℝ) : ℂ) * Complex.I) by
        push_cast
        ring,
    Complex.exp_nat_mul]

/-- `‖∑_{l<K} ζ^l‖ ≤ 2` when `ζ^K = e^{4πit}`, `‖e^{4πit}‖ = 1`, `‖e^{4πit}−1‖ ≤ 2`
and `1 ≤ ‖ζ−1‖`. -/
theorem norm_geom_sum_le_two {K : ℕ} (hK : 0 < K) {ζ E : ℂ}
    (hζK : ζ ^ K = E) (hE : ‖E‖ = 1) (hEsub : ‖E - 1‖ ≤ 2) (hζsub : 1 ≤ ‖ζ - 1‖) :
    ‖E * ∑ l ∈ range K, ζ ^ l‖ ≤ 2 := by
  have hne : ζ ≠ 1 := by
    intro h
    rw [h, sub_self, norm_zero] at hζsub
    linarith
  have hgeom : ∑ l ∈ range K, ζ ^ l = (ζ ^ K - 1) / (ζ - 1) := geom_sum_eq hne K
  rw [hgeom, hζK, norm_mul, hE, one_mul, norm_div]
  have h : ‖E - 1‖ / ‖ζ - 1‖ ≤ 2 / 1 := by
    rw [div_le_div_iff₀ (by positivity : (0:ℝ) < ‖ζ - 1‖) (by norm_num)]
    nlinarith [hEsub, hζsub]
  simpa using h

/-- **`|∑_{l<K} e^{4πit(1+l/K)}| ≤ 2`**, given `|sin(2πt/K)| ≥ 1/2`. -/
theorem norm_Dsum_le_two {K : ℕ} (hK : 1 ≤ K) {t : ℝ}
    (hs : 1 / 2 ≤ |Real.sin (2 * Real.pi * t / (K : ℝ))|) :
    ‖Dsum K t‖ ≤ 2 := by
  have hKpos : (0 : ℝ) < ((K : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < K)
  have hE : ‖Complex.exp (((4 * Real.pi * t : ℝ) : ℂ) * Complex.I)‖ = 1 :=
    Complex.norm_exp_ofReal_mul_I _
  have hEsub : ‖Complex.exp (((4 * Real.pi * t : ℝ) : ℂ) * Complex.I) - 1‖ ≤ 2 := by
    rw [show ((4 * Real.pi * t : ℝ) : ℂ) * Complex.I
        = Complex.I * ((4 * Real.pi * t : ℝ) : ℂ) from mul_comm _ _,
      Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, abs_mul,
      abs_of_pos (by norm_num : (0:ℝ) < 2)]
    have h2 : ((4 * Real.pi * t : ℝ) / 2) = 2 * Real.pi * t := by ring
    rw [h2]
    have hsin := Real.abs_sin_le_one (2 * Real.pi * t)
    linarith
  have hζsub : 1 ≤ ‖Complex.exp (((4 * Real.pi * t / (K : ℝ) : ℝ) : ℂ) * Complex.I) - 1‖ := by
    rw [show ((4 * Real.pi * t / (K : ℝ) : ℝ) : ℂ) * Complex.I
        = Complex.I * ((4 * Real.pi * t / (K : ℝ) : ℝ) : ℂ) from mul_comm _ _,
      Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, abs_mul,
      abs_of_pos (by norm_num : (0:ℝ) < 2)]
    have h2 : ((4 * Real.pi * t / (K : ℝ) : ℝ) / 2) = 2 * Real.pi * t / (K : ℝ) := by
      field_simp
      ring
    rw [h2]
    linarith
  have hex : (((K : ℕ) : ℂ)) * (((4 * Real.pi * t / (K : ℝ) : ℝ) : ℂ) * Complex.I)
      = ((4 * Real.pi * t : ℝ) : ℂ) * Complex.I := by
    push_cast
    have hk : ((K : ℕ) : ℝ) ≠ 0 := hKpos.ne'
    field_simp [hk]
    have hkC : (((K : ℕ) : ℂ)) ≠ 0 := by exact_mod_cast hk
    rw [mul_div_cancel_left₀ _ hkC]
  have hζK : (Complex.exp (((4 * Real.pi * t / (K : ℝ) : ℝ) : ℂ) * Complex.I)) ^ K
      = Complex.exp (((4 * Real.pi * t : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_nat_mul, hex]
  rw [Dsum_factor]
  exact norm_geom_sum_le_two (by omega) hζK hE hEsub hζsub


/-- On the window: `|sin(2πt/K)| = |cos(2π(t−t₀)/K)| ≥ 1/2`. -/
theorem sin_window {K : ℕ} (hK : 1 ≤ K) {u t : ℝ} (hu : 3 / 50 ≤ u)
    (ht : |t - (K : ℝ) / 4| ≤ (K : ℝ) / (100 * u)) :
    1 / 2 ≤ |Real.sin (2 * Real.pi * t / (K : ℝ))| := by
  have hK0 : (0 : ℝ) < ((K : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < K)
  have hupos : 0 < u := by linarith
  have habs : |2 * Real.pi * (t - (K : ℝ) / 4)| = 2 * Real.pi * |t - (K : ℝ) / 4| := by
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2), abs_of_pos Real.pi_pos]
  have hx : |2 * Real.pi * (t - (K : ℝ) / 4) / (K : ℝ)| ≤ Real.pi / 3 := by
    rw [abs_div, habs, abs_of_pos hK0]
    have h1 : 2 * Real.pi * |t - (K : ℝ) / 4| ≤ 2 * Real.pi * ((K : ℝ) / (100 * u)) :=
      mul_le_mul_of_nonneg_left ht (by positivity)
    have h2 : 2 * Real.pi * ((K : ℝ) / (100 * u)) / (K : ℝ) = Real.pi / (50 * u) := by
      field_simp
      ring
    have h3 : Real.pi / (50 * u) ≤ Real.pi / 3 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [Real.pi_pos]
    have hstep : 2 * Real.pi * |t - (K : ℝ) / 4| / (K : ℝ)
        ≤ 2 * Real.pi * ((K : ℝ) / (100 * u)) / (K : ℝ) := by
      apply div_le_div_of_nonneg_right _ (le_of_lt hK0)
      linarith
    linarith [hstep, h2, h3]
  have harg : 2 * Real.pi * t / (K : ℝ)
      = 2 * Real.pi * (t - (K : ℝ) / 4) / (K : ℝ) + Real.pi / 2 := by
    field_simp
    ring
  rw [harg, Real.sin_add_pi_div_two]
  have hxabs : |2 * Real.pi * (t - (K : ℝ) / 4) / (K : ℝ)| ≤ Real.pi / 2 := by
    have h : Real.pi / 3 ≤ Real.pi / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [Real.pi_pos]
    linarith
  have hcos : 0 ≤ Real.cos (2 * Real.pi * (t - (K : ℝ) / 4) / (K : ℝ)) := by
    refine Real.cos_nonneg_of_mem_Icc ?_
    rw [Set.mem_Icc, ← abs_le]
    exact hxabs
  rw [abs_of_nonneg hcos]
  have hmono := Real.cos_le_cos_of_nonneg_of_le_pi
    (x := |2 * Real.pi * (t - (K : ℝ) / 4) / (K : ℝ)|) (y := Real.pi / 3)
    (abs_nonneg _) (by have := Real.pi_pos; nlinarith) hx
  rw [Real.cos_abs] at hmono
  rw [Real.cos_pi_div_three] at hmono
  exact hmono

/-- `|V_K(t) − K/4| ≤ 1/2` given `|sin(2πt/K)| ≥ 1/2`. -/
theorem abs_VK_sub_center {K : ℕ} (hK : 1 ≤ K) {t : ℝ}
    (hs : 1 / 2 ≤ |Real.sin (2 * Real.pi * t / (K : ℝ))|) :
    |VK K t - (K : ℝ) / 4| ≤ 1 / 2 := by
  have hre : |∑ l ∈ range K, Real.cos (4 * Real.pi * t * (1 + (l : ℝ) / (K : ℝ)))| ≤ 2 := by
    rw [← Dsum_re]
    exact (Complex.abs_re_le_norm _).trans (norm_Dsum_le_two hK hs)
  rw [VK_eq_center_sub]
  have h : ((K : ℝ) / 4 - 1 / 4 * ∑ l ∈ range K,
        Real.cos (4 * Real.pi * t * (1 + (l : ℝ) / (K : ℝ)))) - (K : ℝ) / 4
      = -(1 / 4 * ∑ l ∈ range K, Real.cos (4 * Real.pi * t * (1 + (l : ℝ) / (K : ℝ)))) := by
    ring
  rw [h, abs_neg, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 1 / 4)]
  have h2 : (1 / 4 : ℝ) * |∑ l ∈ range K,
      Real.cos (4 * Real.pi * t * (1 + (l : ℝ) / (K : ℝ)))| ≤ (1 / 4 : ℝ) * 2 :=
    mul_le_mul_of_nonneg_left hre (by norm_num)
  linarith

/-- **The variance half of `eq:window-bounds`**: `|V_K(t) − K/4| ≤ 1/2` and
`K/8 ≤ V_K(t) ≤ 3K/8`, for `K ≥ 4`, `u ≥ 3/50` and `t ∈ W_{K,u}`. -/
theorem VK_window {K : ℕ} (hK : 4 ≤ K) {u t : ℝ} (hu : 3 / 50 ≤ u)
    (ht : |t - (K : ℝ) / 4| ≤ (K : ℝ) / (100 * u)) :
    |VK K t - (K : ℝ) / 4| ≤ 1 / 2
      ∧ (K : ℝ) / 8 ≤ VK K t ∧ VK K t ≤ 3 * (K : ℝ) / 8 := by
  have hK1 : 1 ≤ K := by omega
  have hs := sin_window hK1 hu ht
  have hsub := abs_VK_sub_center hK1 hs
  have hK0 : (0 : ℝ) < ((K : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < K)
  have hle := (abs_le.mp hsub).1
  have hge := (abs_le.mp hsub).2
  constructor
  · exact hsub
  constructor
  · have : (K : ℝ) / 8 ≤ (K : ℝ) / 4 - 1 / 2 := by
      have h4 : (4 : ℝ) ≤ ((K : ℕ) : ℝ) := by exact_mod_cast hK
      rw [div_le_iff₀ (by norm_num : (0:ℝ) < 8), sub_mul]
      ring_nf
      nlinarith
    linarith
  · have : (K : ℝ) / 4 + 1 / 2 ≤ 3 * (K : ℝ) / 8 := by
      have h4 : (4 : ℝ) ≤ ((K : ℕ) : ℝ) := by exact_mod_cast hK
      rw [le_div_iff₀ (by norm_num : (0:ℝ) < 8), add_mul]
      ring_nf
      nlinarith
    linarith

/-- **`lem:bounded` in full on the window**: `|S_t(x)|/√(V_K(t)) ≤ 5√8`. -/
theorem abs_Y_le_window {K : ℕ} (hK : 4 ≤ K) {u t x : ℝ} (hu : 3 / 50 ≤ u)
    (ht : |t - (K : ℝ) / 4| ≤ (K : ℝ) / (100 * u)) :
    |Sfun K t x| / Real.sqrt (VK K t) ≤ 5 * Real.sqrt 8 :=
  abs_Y_le (by omega) t x (VK_window hK hu ht).2.1

end RudinDensity
end CenteredCube

#print axioms CenteredCube.RudinDensity.VK_eq_center_sub
#print axioms CenteredCube.RudinDensity.rfun_window
#print axioms CenteredCube.RudinDensity.Dsum_re
#print axioms CenteredCube.RudinDensity.Dsum_factor
#print axioms CenteredCube.RudinDensity.norm_geom_sum_le_two
#print axioms CenteredCube.RudinDensity.norm_Dsum_le_two
#print axioms CenteredCube.RudinDensity.sin_window
#print axioms CenteredCube.RudinDensity.abs_VK_sub_center
#print axioms CenteredCube.RudinDensity.VK_window
#print axioms CenteredCube.RudinDensity.abs_Y_le_window
