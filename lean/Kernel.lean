/-
The scale covariance `κ_K` and Lemma `lem:finite-kernel`.

`Y_t = S_t/√(V_K(t))` is the standardised variable of the manuscript, and

  `κ_K(t,s) = E[Y_t(U)Y_s(U)] = (∫₀¹ S_t S_s) / √(V_K(t)V_K(s))`
            `= [Re D_K(t−s) − Re D_K(t+s)] / l_{t,s}`,

by eq. (3.4) (`integral_Sfun_mul_eq_DK`), with the normalising factor
`l_{t,s} = 4√(V_K(t)V_K(s))/K = √((1+e_t)(1+e_s))`.

On the window (`K ≥ 4`, `u ≥ 3/50`, `|t−t₀|, |s−t₀| ≤ K/(100u)`):
`1 − 2/K ≤ l_{t,s} ≤ 1 + 2/K`, `|Re D_K(t+s)| ≤ 2/K`, and therefore

  `|κ_K(t,s) − Re D_K(t−s)| ≤ 8/K`,

which is `lem:finite-kernel`.  The continuous-kernel, quadratic and global
lemmas that consume it are *not* proved here.
-/
import ClosedForm

open Finset MeasureTheory intervalIntegral
open scoped BigOperators

namespace CenteredCube
namespace RudinDensity

/-- The scale covariance `κ_K(t,s) = E[Y_t(U)Y_s(U)]` with `Y_t = S_t/√(V_K(t))`. -/
noncomputable def kappa (K : ℕ) (t s : ℝ) : ℝ :=
  (∫ x in (0 : ℝ)..1, Sfun K t x * Sfun K s x) / Real.sqrt (VK K t * VK K s)

/-- The normalising factor `l_{t,s} = 4√(V_K(t)V_K(s))/K = √((1+e_t)(1+e_s))`. -/
noncomputable def lts (K : ℕ) (t s : ℝ) : ℝ := 4 * Real.sqrt (VK K t * VK K s) / (K : ℝ)

/-- `κ_K(t,s) = [Re D_K(t−s) − Re D_K(t+s)] / l_{t,s}`. -/
theorem kappa_eq {K : ℕ} (hK : 1 ≤ K) (t s : ℝ) (hVt : 0 < VK K t) (hVs : 0 < VK K s) :
    kappa K t s = (ReDK K (t - s) - ReDK K (t + s)) / lts K t s := by
  have hK0 : (0 : ℝ) < ((K : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < K)
  have hsqrt : 0 < Real.sqrt (VK K t * VK K s) := by
    rw [Real.sqrt_pos]
    exact mul_pos hVt hVs
  unfold kappa lts
  rw [integral_Sfun_mul_eq_DK hK t s]
  field_simp


/-- On the window: `|sin(π(t+s)/K)| ≥ 1/2`, since `t+s = K/2 + (t−t₀) + (s−t₀)`. -/
theorem sin_add_window {K : ℕ} (hK : 1 ≤ K) {u t s : ℝ} (hu : 3 / 50 ≤ u)
    (ht : |t - (K : ℝ) / 4| ≤ (K : ℝ) / (100 * u))
    (hs : |s - (K : ℝ) / 4| ≤ (K : ℝ) / (100 * u)) :
    1 / 2 ≤ |Real.sin (Real.pi * (t + s) / (K : ℝ))| := by
  have hK0 : (0 : ℝ) < ((K : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < K)
  have hupos : 0 < u := by linarith
  have hδ : |(t - (K : ℝ) / 4) + (s - (K : ℝ) / 4)| ≤ (K : ℝ) / (50 * u) := by
    have := abs_add_le (t - (K : ℝ) / 4) (s - (K : ℝ) / 4)
    have h1 : |t - (K : ℝ) / 4| + |s - (K : ℝ) / 4| ≤ (K : ℝ) / (100 * u) + (K : ℝ) / (100 * u) := by
      linarith
    have h2 : (K : ℝ) / (100 * u) + (K : ℝ) / (100 * u) = (K : ℝ) / (50 * u) := by
      field_simp
      ring
    linarith
  have hx : |Real.pi * ((t - (K : ℝ) / 4) + (s - (K : ℝ) / 4)) / (K : ℝ)| ≤ Real.pi / 3 := by
    rw [abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos hK0]
    have h1 : Real.pi * |(t - (K : ℝ) / 4) + (s - (K : ℝ) / 4)| ≤ Real.pi * ((K : ℝ) / (50 * u)) :=
      mul_le_mul_of_nonneg_left hδ Real.pi_pos.le
    have h2 : Real.pi * ((K : ℝ) / (50 * u)) / (K : ℝ) = Real.pi / (50 * u) := by
      field_simp
    have h3 : Real.pi / (50 * u) ≤ Real.pi / 3 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [Real.pi_pos]
    have hstep : Real.pi * |(t - (K : ℝ) / 4) + (s - (K : ℝ) / 4)| / (K : ℝ)
        ≤ Real.pi * ((K : ℝ) / (50 * u)) / (K : ℝ) := by
      apply div_le_div_of_nonneg_right _ (le_of_lt hK0)
      linarith
    linarith [hstep, h2, h3]
  have harg : Real.pi * (t + s) / (K : ℝ)
      = Real.pi * ((t - (K : ℝ) / 4) + (s - (K : ℝ) / 4)) / (K : ℝ) + Real.pi / 2 := by
    field_simp
    ring
  rw [harg, Real.sin_add_pi_div_two]
  have hxabs : |Real.pi * ((t - (K : ℝ) / 4) + (s - (K : ℝ) / 4)) / (K : ℝ)| ≤ Real.pi / 2 := by
    have h : Real.pi / 3 ≤ Real.pi / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [Real.pi_pos]
    linarith
  have hcos : 0 ≤ Real.cos (Real.pi * ((t - (K : ℝ) / 4) + (s - (K : ℝ) / 4)) / (K : ℝ)) := by
    refine Real.cos_nonneg_of_mem_Icc ?_
    rw [Set.mem_Icc, ← abs_le]
    exact hxabs
  rw [abs_of_nonneg hcos]
  have hmono := Real.cos_le_cos_of_nonneg_of_le_pi
    (x := |Real.pi * ((t - (K : ℝ) / 4) + (s - (K : ℝ) / 4)) / (K : ℝ)|) (y := Real.pi / 3)
    (abs_nonneg _) (by have := Real.pi_pos; nlinarith) hx
  rw [Real.cos_abs] at hmono
  rw [Real.cos_pi_div_three] at hmono
  exact hmono

/-- `|Re D_K(t+s)| ≤ 2/K` on the window. -/
theorem abs_ReDK_add_le {K : ℕ} (hK : 4 ≤ K) {u t s : ℝ} (hu : 3 / 50 ≤ u)
    (ht : |t - (K : ℝ) / 4| ≤ (K : ℝ) / (100 * u))
    (hs : |s - (K : ℝ) / 4| ≤ (K : ℝ) / (100 * u)) :
    |ReDK K (t + s)| ≤ 2 / (K : ℝ) := by
  have hK1 : 1 ≤ K := by omega
  have hK0 : (0 : ℝ) < ((K : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < K)
  have hsin : Real.sin (Real.pi * (t + s) / (K : ℝ)) ≠ 0 := by
    have := sin_add_window hK1 hu ht hs
    intro h
    rw [h, abs_zero] at this
    linarith
  have hnorm : ‖DK K (t + s)‖
      = |Real.sin (Real.pi * (t + s))|
        / (((K : ℕ) : ℝ) * |Real.sin (Real.pi * (t + s) / (K : ℝ))|) :=
    norm_DK_eq hK1 hsin
  have hnum : |Real.sin (Real.pi * (t + s))| ≤ 1 := Real.abs_sin_le_one _
  have hden : 1 / 2 ≤ |Real.sin (Real.pi * (t + s) / (K : ℝ))| := sin_add_window hK1 hu ht hs
  have hfrac : |Real.sin (Real.pi * (t + s))|
      / (((K : ℕ) : ℝ) * |Real.sin (Real.pi * (t + s) / (K : ℝ))|) ≤ 2 / (K : ℝ) := by
    have hpos : 0 < ((K : ℕ) : ℝ) * |Real.sin (Real.pi * (t + s) / (K : ℝ))| := by positivity
    have hstep : |Real.sin (Real.pi * (t + s))|
        / (((K : ℕ) : ℝ) * |Real.sin (Real.pi * (t + s) / (K : ℝ))|)
        ≤ 1 / (((K : ℕ) : ℝ) * |Real.sin (Real.pi * (t + s) / (K : ℝ))|) :=
      div_le_div_of_nonneg_right hnum (le_of_lt hpos)
    have hstep2 : 1 / (((K : ℕ) : ℝ) * |Real.sin (Real.pi * (t + s) / (K : ℝ))|)
        ≤ 2 / (K : ℝ) := by
      rw [div_le_div_iff₀ hpos hK0]
      have h2m : (1:ℝ) ≤ 2 * |Real.sin (Real.pi * (t + s) / (K : ℝ))| := by linarith
      have hKm : ((K : ℕ) : ℝ) ≤ 2 * (((K : ℕ) : ℝ) * |Real.sin (Real.pi * (t + s) / (K : ℝ))|) := by
        have h := mul_le_mul_of_nonneg_left h2m hK0.le
        rw [mul_one,
          show ((K : ℕ) : ℝ) * (2 * |Real.sin (Real.pi * (t + s) / (K : ℝ))|)
            = 2 * (((K : ℕ) : ℝ) * |Real.sin (Real.pi * (t + s) / (K : ℝ))|) by ring] at h
        exact h
      linarith
    linarith [hstep, hstep2]

  have : |(DK K (t + s)).re| ≤ ‖DK K (t + s)‖ := Complex.abs_re_le_norm _
  rw [hnorm] at this
  rw [ReDK]
  linarith


/-- `|Re D_K(τ)| ≤ 1` for `K ≥ 1`. -/
theorem abs_ReDK_le {K : ℕ} (hK : 0 < K) (τ : ℝ) : |ReDK K τ| ≤ 1 := by
  have : |(DK K τ).re| ≤ ‖DK K τ‖ := Complex.abs_re_le_norm _
  rw [ReDK]
  exact this.trans (norm_DK_le hK τ)

/-- On the window: `1 − 2/K ≤ l_{t,s} ≤ 1 + 2/K`. -/
theorem lts_bounds {K : ℕ} (hK : 4 ≤ K) {u t s : ℝ} (hu : 3 / 50 ≤ u)
    (ht : |t - (K : ℝ) / 4| ≤ (K : ℝ) / (100 * u))
    (hs : |s - (K : ℝ) / 4| ≤ (K : ℝ) / (100 * u)) :
    1 - 2 / (K : ℝ) ≤ lts K t s ∧ lts K t s ≤ 1 + 2 / (K : ℝ) := by
  have hK1 : 1 ≤ K := by omega
  have hK0 : (0 : ℝ) < ((K : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < K)
  have hVtW := (VK_window hK hu ht).2
  have hVsW := (VK_window hK hu hs).2
  have hsub : |VK K t - (K : ℝ) / 4| ≤ 1 / 2 := (VK_window hK hu ht).1
  have hsub2 : |VK K s - (K : ℝ) / 4| ≤ 1 / 2 := (VK_window hK hu hs).1
  have hVtle : VK K t ≤ (K : ℝ) / 4 + 1 / 2 := by linarith [abs_le.mp hsub |>.2]
  have hVtge : (K : ℝ) / 4 - 1 / 2 ≤ VK K t := by linarith [abs_le.mp hsub |>.1]
  have hVsle : VK K s ≤ (K : ℝ) / 4 + 1 / 2 := by linarith [abs_le.mp hsub2 |>.2]
  have hVsge : (K : ℝ) / 4 - 1 / 2 ≤ VK K s := by linarith [abs_le.mp hsub2 |>.1]
  have hlo : (0 : ℝ) ≤ (K : ℝ) / 4 - 1 / 2 := by
    have h4 : (4:ℝ) ≤ ((K:ℕ):ℝ) := by exact_mod_cast hK
    linarith
  have hprodlo : ((K : ℝ) / 4 - 1 / 2) ^ 2 ≤ VK K t * VK K s := by
    nlinarith [hVtge, hVsge, hVtle, hVsle, hlo]
  have hprodhi : VK K t * VK K s ≤ ((K : ℝ) / 4 + 1 / 2) ^ 2 := by
    nlinarith [hVtge, hVsge, hVtle, hVsle, hlo]
  have hVt : 0 < VK K t := lt_of_lt_of_le (by positivity : (0:ℝ) < (K:ℝ)/8) hVtW.1
  have hVs : 0 < VK K s := lt_of_lt_of_le (by positivity : (0:ℝ) < (K:ℝ)/8) hVsW.1
  have hsqrtlo : (K : ℝ) / 4 - 1 / 2 ≤ Real.sqrt (VK K t * VK K s) := by
    rw [Real.le_sqrt hlo (le_of_lt (mul_pos hVt hVs))]
    exact hprodlo
  have hsqrthi : Real.sqrt (VK K t * VK K s) ≤ (K : ℝ) / 4 + 1 / 2 := by
    rw [Real.sqrt_le_left (by positivity : (0:ℝ) ≤ (K:ℝ)/4 + 1/2)]
    exact hprodhi
  have hlo2 : 1 - 2 / (K : ℝ) ≤ lts K t s := by
    unfold lts
    rw [le_div_iff₀ hK0]
    have hkey : (1 - 2 / ((K : ℕ) : ℝ)) * ((K : ℕ) : ℝ) = ((K : ℕ) : ℝ) - 2 := by
      field_simp
    rw [hkey]
    have hsub4 : ((K : ℝ) / 4 - 1 / 2) * 4 = ((K : ℕ) : ℝ) - 2 := by ring
    have h : ((K : ℕ) : ℝ) - 2 ≤ Real.sqrt (VK K t * VK K s) * 4 := by
      rw [← hsub4]
      exact mul_le_mul_of_nonneg_right hsqrtlo (by norm_num)
    have h2 : Real.sqrt (VK K t * VK K s) * 4 = 4 * Real.sqrt (VK K t * VK K s) := by ring
    rw [h2] at h
    exact h
  have hhi2 : lts K t s ≤ 1 + 2 / (K : ℝ) := by
    unfold lts
    rw [div_le_iff₀ hK0]
    have hkey : (1 + 2 / ((K : ℕ) : ℝ)) * ((K : ℕ) : ℝ) = ((K : ℕ) : ℝ) + 2 := by
      field_simp
    rw [hkey]
    have hsub4 : ((K : ℝ) / 4 + 1 / 2) * 4 = ((K : ℕ) : ℝ) + 2 := by ring
    have h : Real.sqrt (VK K t * VK K s) * 4 ≤ ((K : ℕ) : ℝ) + 2 := by
      rw [← hsub4]
      exact mul_le_mul_of_nonneg_right hsqrthi (by norm_num)
    have h2 : Real.sqrt (VK K t * VK K s) * 4 = 4 * Real.sqrt (VK K t * VK K s) := by ring
    rw [h2] at h
    exact h
  exact ⟨hlo2, hhi2⟩

/-- **`lem:finite-kernel`**: `|κ_K(t,s) − Re D_K(t−s)| ≤ 8/K` on the window. -/
theorem finite_kernel {K : ℕ} (hK : 4 ≤ K) {u t s : ℝ} (hu : 3 / 50 ≤ u)
    (ht : |t - (K : ℝ) / 4| ≤ (K : ℝ) / (100 * u))
    (hs : |s - (K : ℝ) / 4| ≤ (K : ℝ) / (100 * u)) :
    |kappa K t s - ReDK K (t - s)| ≤ 8 / (K : ℝ) := by
  have hK1 : 1 ≤ K := by omega
  have hK0 : (0 : ℝ) < ((K : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < K)
  have hVt : 0 < VK K t := lt_of_lt_of_le (by positivity : (0:ℝ) < (K:ℝ)/8)
    (VK_window hK hu ht).2.1
  have hVs : 0 < VK K s := lt_of_lt_of_le (by positivity : (0:ℝ) < (K:ℝ)/8)
    (VK_window hK hu hs).2.1
  have hlb := (lts_bounds hK hu ht hs).1
  have hub := (lts_bounds hK hu ht hs).2
  have hlpos : 0 < lts K t s := by
    have : (0:ℝ) < 1 - 2 / (K:ℝ) := by
      have h4 : (4:ℝ) ≤ ((K:ℕ):ℝ) := by exact_mod_cast hK
      have : (2:ℝ) / (K:ℝ) ≤ 1/2 := by
        rw [div_le_div_iff₀ hK0 (by norm_num)]
        nlinarith
      linarith
    linarith
  have hRe_le : |ReDK K (t - s)| ≤ 1 := abs_ReDK_le (by omega) (t - s)
  have hRe_add : |ReDK K (t + s)| ≤ 2 / (K : ℝ) := abs_ReDK_add_le hK hu ht hs
  have hkap : kappa K t s = (ReDK K (t - s) - ReDK K (t + s)) / lts K t s :=
    kappa_eq hK1 t s hVt hVs
  have hden : 1 - 2 / (K : ℝ) ≤ lts K t s := hlb
  have hhalf : (1:ℝ) / 2 ≤ lts K t s := by
    have h4 : (4:ℝ) ≤ ((K:ℕ):ℝ) := by exact_mod_cast hK
    have : (2:ℝ) / (K:ℝ) ≤ 1/2 := by
      rw [div_le_div_iff₀ hK0 (by norm_num)]
      nlinarith
    linarith
  have hlt : |1 - lts K t s| ≤ 2 / (K : ℝ) := by
    rw [abs_sub_comm]
    have h1 : lts K t s - 1 ≤ 2 / (K : ℝ) := by linarith
    have h2 : 1 - lts K t s ≤ 2 / (K : ℝ) := by linarith
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hnum : |ReDK K (t - s) * (1 - lts K t s) - ReDK K (t + s)| ≤ 4 / (K : ℝ) := by
    have h1 := abs_sub (ReDK K (t - s) * (1 - lts K t s)) (ReDK K (t + s))
    rw [abs_mul] at h1
    have h2 : |ReDK K (t - s)| * |1 - lts K t s| ≤ 2 / (K : ℝ) := by
      have h := mul_le_mul hRe_le hlt (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
      rw [one_mul] at h
      exact h
    have hsum : 2 / (K : ℝ) + 2 / (K : ℝ) = 4 / (K : ℝ) := by
      field_simp
      ring
    linarith [h1, h2, hRe_add, hsum]
  have hquot : |kappa K t s - ReDK K (t - s)| ≤ 8 / (K : ℝ) := by
    rw [hkap]
    have hform : (ReDK K (t - s) - ReDK K (t + s)) / lts K t s - ReDK K (t - s)
        = (ReDK K (t - s) * (1 - lts K t s) - ReDK K (t + s)) / lts K t s := by
      rw [sub_div]
      field_simp
      ring
    rw [hform, abs_div, abs_of_pos hlpos]
    have hstep : |ReDK K (t - s) * (1 - lts K t s) - ReDK K (t + s)| / lts K t s
        ≤ (4 / (K : ℝ)) / (1 / 2) := by
      have hstep1 : |ReDK K (t - s) * (1 - lts K t s) - ReDK K (t + s)| / lts K t s
          ≤ (4 / (K : ℝ)) / lts K t s :=
        div_le_div_of_nonneg_right hnum (le_of_lt hlpos)
      have hstep2 : (4 / (K : ℝ)) / lts K t s ≤ (4 / (K : ℝ)) / (1 / 2) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hhalf
      linarith
    have hval : (4 / (K : ℝ)) / (1 / 2) = 8 / (K : ℝ) := by
      field_simp
      ring
    linarith [hstep, hval]
  exact hquot

end RudinDensity
end CenteredCube

#print axioms CenteredCube.RudinDensity.kappa_eq
#print axioms CenteredCube.RudinDensity.sin_add_window
#print axioms CenteredCube.RudinDensity.abs_ReDK_add_le
#print axioms CenteredCube.RudinDensity.abs_ReDK_le
#print axioms CenteredCube.RudinDensity.lts_bounds
#print axioms CenteredCube.RudinDensity.finite_kernel
