/-
The centre of the variance window: equation `eq:center` of the manuscript.

`eq:variances` gives `V_K(t) = ½ ∑_{l<K} sin²(2πt(1+l/K))` and
`σ_t² = V_K(t)/(900π²K³r(t)²)`.  At the centre `t_0 = K/4` (so that `r(t_0) = 3/2`)
the sine factor becomes `sin(π(K+l)/2)`, which is `±1` exactly at odd `l`.  For
`4 ∣ K` there are `K/2` odd indices, hence

  `V_K(t_0) = K/4`,   `σ_{t_0} = 1/(90πK)`,

which is `eq:center`; `u = √n σ_{t_0} = √n/(90πK)` in `main-proof.tex` follows.

This file also records `E d_t² = σ_t²` (`integral_d_sq`), i.e. that the definition
of `sigmaSq` is the second moment of the normalised average.
-/
import Average

open Finset
open scoped BigOperators

namespace CenteredCube
namespace RudinDensity

/-- The variance profile `V_K(t) = ½ ∑_{l<K} sin²(2πt(1+l/K))` of `eq:variances`. -/
noncomputable def VK (K : ℕ) (t : ℝ) : ℝ :=
  1 / 2 * ∑ l ∈ range K, (Real.sin (2 * Real.pi * t * (1 + (l : ℝ) / (K : ℝ)))) ^ 2

/-- `∑_{l<2q} (-1)^l = 0`. -/
theorem sum_range_neg_one_pow_two_mul (q : ℕ) :
    ∑ l ∈ range (2 * q), (-1 : ℝ) ^ l = 0 := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [show 2 * (q + 1) = 2 * q + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih]
    have h1 : (-1 : ℝ) ^ (2 * q) = 1 := Even.neg_one_pow ⟨q, by ring⟩
    have h2 : (-1 : ℝ) ^ (2 * q + 1) = -1 := Odd.neg_one_pow ⟨q, by ring⟩
    rw [h1, h2]
    ring

/-- **The centre value `V_K(t_0) = K/4`** of `eq:center`, at `t_0 = K/4` with `4 ∣ K`:
the sine factor becomes `sin(π(K+l)/2)`, whose square is `1` exactly at odd `l`, and
there are `K/2` of those. -/
theorem VK_center {K : ℕ} (h4 : 4 ∣ K) :
    VK K ((K : ℝ) / 4) = (K : ℝ) / 4 := by
  obtain ⟨q, rfl⟩ := h4
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp [VK]
  · have hK0 : ((4 * q : ℕ) : ℝ) ≠ 0 := by
      have : 0 < 4 * q := by omega
      exact_mod_cast this.ne'
    have harg : ∀ l : ℕ, 2 * Real.pi * (((4 * q : ℕ) : ℝ) / 4)
        * (1 + (l : ℝ) / ((4 * q : ℕ) : ℝ))
        = Real.pi * (((4 * q + l : ℕ)) : ℝ) / 2 := by
      intro l
      field_simp
      push_cast
      ring
    have hterm : ∀ l ∈ range (4 * q),
        (Real.sin (2 * Real.pi * (((4 * q : ℕ) : ℝ) / 4)
          * (1 + (l : ℝ) / ((4 * q : ℕ) : ℝ)))) ^ 2
          = 1 / 2 - (-1 : ℝ) ^ l / 2 := by
      intro l _
      rw [harg l, Real.sin_sq_eq_half_sub]
      have hcos : Real.cos (2 * (Real.pi * (((4 * q + l : ℕ)) : ℝ) / 2))
          = (-1 : ℝ) ^ l := by
        rw [show 2 * (Real.pi * (((4 * q + l : ℕ)) : ℝ) / 2)
            = (((4 * q + l : ℕ)) : ℝ) * Real.pi by ring, Real.cos_nat_mul_pi]
        rw [show (4 * q + l : ℕ) = 4 * q + l by rfl, pow_add]
        have h4q : (-1 : ℝ) ^ (4 * q) = 1 := Even.neg_one_pow ⟨2 * q, by ring⟩
        rw [h4q, one_mul]
      rw [hcos]
    rw [VK, Finset.sum_congr rfl hterm]
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hsum0 : (∑ x ∈ range (4 * q), (-1 : ℝ) ^ x / 2) = 0 := by
      rw [← Finset.sum_div, show (4 * q : ℕ) = 2 * (2 * q) by ring,
        sum_range_neg_one_pow_two_mul]
      ring
    rw [hsum0]
    push_cast
    ring

/-- `r(t_0) = 3/2` at `t_0 = K/4`. -/
theorem rfun_center {K : ℕ} (hK : 1 ≤ K) : rfun K ((K : ℝ) / 4) = 3 / 2 := by
  have hK0 : ((K : ℕ) : ℝ) ≠ 0 := by positivity
  unfold rfun
  field_simp
  ring

/-- `σ_t² = V_K(t)/(900π²K³r(t)²)`, the second relation of `eq:variances`. -/
noncomputable def sigmaSq (K : ℕ) (t : ℝ) : ℝ :=
  VK K t / (900 * Real.pi ^ 2 * (K : ℝ) ^ 3 * (rfun K t) ^ 2)

/-- The standard deviation `σ_t`. -/
noncomputable def sigma (K : ℕ) (t : ℝ) : ℝ := Real.sqrt (sigmaSq K t)

/-- **`E d_t² = σ_t²`**: the definition of `sigmaSq` is the second moment of the
normalised average `d_t = S_t/(30πK^{3/2}r(t))`, by `integral_scaled_sq`. -/
theorem integral_d_sq {K : ℕ} (hK : 1 ≤ K) (t : ℝ) (hr : 0 < rfun K t) :
    ∫ x in (0 : ℝ)..1,
        (Sfun K t x / (30 * Real.pi * (K : ℝ) * Real.sqrt (K : ℝ) * rfun K t)) ^ 2
      = sigmaSq K t := by
  have hK0 : (0 : ℝ) < (K : ℝ) := by exact_mod_cast (by omega : 0 < K)
  have hc : (30 * Real.pi * (K : ℝ) * Real.sqrt (K : ℝ) * rfun K t) ≠ 0 := by positivity
  rw [integral_scaled_sq K hK t hc]
  have hsqrt : (Real.sqrt (K : ℝ)) ^ 2 = (K : ℝ) := Real.sq_sqrt hK0.le
  unfold sigmaSq VK
  rw [show (30 * Real.pi * (K : ℝ) * Real.sqrt (K : ℝ) * rfun K t) ^ 2
      = 900 * Real.pi ^ 2 * (K : ℝ) ^ 3 * (rfun K t) ^ 2 by
    rw [mul_pow, mul_pow, mul_pow, mul_pow, hsqrt]
    ring]

/-- **`V_K(t_0) = K/4` and `σ_{t_0} = 1/(90πK)`**: the value of `σ_t²` at the centre. -/
theorem sigmaSq_center {K : ℕ} (hK : 1 ≤ K) (h4 : 4 ∣ K) :
    sigmaSq K ((K : ℝ) / 4) = 1 / (8100 * Real.pi ^ 2 * (K : ℝ) ^ 2) := by
  have hK0 : ((K : ℕ) : ℝ) ≠ 0 := by positivity
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  unfold sigmaSq
  rw [VK_center h4, rfun_center hK]
  field_simp
  ring

/-- **`σ_{t_0} = 1/(90πK)`** — the second half of `eq:center`. -/
theorem sigma_center {K : ℕ} (hK : 1 ≤ K) (h4 : 4 ∣ K) :
    sigma K ((K : ℝ) / 4) = 1 / (90 * Real.pi * (K : ℝ)) := by
  have hK0 : ((K : ℕ) : ℝ) ≠ 0 := by positivity
  have hsq : (1 / (90 * Real.pi * (K : ℝ))) ^ 2
      = 1 / (8100 * Real.pi ^ 2 * (K : ℝ) ^ 2) := by
    field_simp
    ring
  unfold sigma
  rw [sigmaSq_center hK h4, ← hsq, Real.sqrt_sq (by positivity)]

end RudinDensity
end CenteredCube

#print axioms CenteredCube.RudinDensity.sum_range_neg_one_pow_two_mul
#print axioms CenteredCube.RudinDensity.VK_center
#print axioms CenteredCube.RudinDensity.rfun_center
#print axioms CenteredCube.RudinDensity.integral_d_sq
#print axioms CenteredCube.RudinDensity.sigmaSq_center
#print axioms CenteredCube.RudinDensity.sigma_center
