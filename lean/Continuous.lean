/-
The continuous kernel `R` and Lemma `lem:continuous-kernel`.

`R(τ) = ∫_1^2 cos(2πτy) dy` is the real part of `𝒦(τ) = ∫_1^2 e^{2πiτy} dy`.
Partitioning `[1,2]` into the `K` intervals `I_l = [1+l/K, 1+(l+1)/K]`, the
left-endpoint sample `D_K(τ) = (1/K)∑_{l<K} e^{2πiτ(1+l/K)}` differs from `𝒦(τ)`
by at most `2πH/K` for `|τ| ≤ H`: on each interval the integrand varies by at
most `2πH/K`, so the sampling error is `2πH/K²`, and the `K` errors sum to
`2πH/K`.  Taking real parts,

  `|Re D_K(τ) − R(τ)| ≤ 2πH/K`.

With `lem:finite-kernel` and the triangle inequality this gives, for
`t, s ∈ W_{K,u}` with `|t − s| ≤ H`,

  `|κ_K(t,s) − R(t−s)| ≤ (2πH + 8)/K`,

which is `lem:continuous-kernel`.  The Taylor expansion of `R` and the
consuming lemmas (`lem:quadratic`, `lem:global`) are not proved here.
-/
import Kernel

open Finset MeasureTheory intervalIntegral
open scoped BigOperators

namespace CenteredCube
namespace RudinDensity

/-- The continuous kernel `R(τ) = ∫_1^2 cos(2πτy) dy`. -/
noncomputable def Rfun (τ : ℝ) : ℝ := ∫ y in (1 : ℝ)..2, Real.cos (2 * Real.pi * τ * y)

/-- `|cos x − cos y| ≤ |x − y|`. -/
theorem abs_cos_sub_abs (x y : ℝ) : |Real.cos x - Real.cos y| ≤ |x - y| := by
  have h1 : |Real.sin ((x + y) / 2)| ≤ 1 := Real.abs_sin_le_one _
  have h2 : |Real.sin ((x - y) / 2)| ≤ |(x - y) / 2| := Real.abs_sin_le_abs
  have h2' : |(x - y) / 2| = |x - y| / 2 := by
    rw [abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2)]
  have hmul : |Real.sin ((x + y) / 2)| * |Real.sin ((x - y) / 2)| ≤ |x - y| / 2 := by
    calc |Real.sin ((x + y) / 2)| * |Real.sin ((x - y) / 2)|
        ≤ 1 * |Real.sin ((x - y) / 2)| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
      _ = |Real.sin ((x - y) / 2)| := one_mul _
      _ ≤ |(x - y) / 2| := h2
      _ = |x - y| / 2 := h2'
  rw [Real.cos_sub_cos, abs_mul, abs_mul, abs_neg,
    abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  have : 2 * (|Real.sin ((x + y) / 2)| * |Real.sin ((x - y) / 2)|) ≤ 2 * (|x - y| / 2) :=
    mul_le_mul_of_nonneg_left hmul (by norm_num)
  ring_nf at this ⊢
  linarith

/-- `|cos(2πτa) − cos(2πτb)| ≤ 2π|τ|·|a−b|`. -/
theorem abs_cos_sub_le (τ a b : ℝ) :
    |Real.cos (2 * Real.pi * τ * a) - Real.cos (2 * Real.pi * τ * b)|
      ≤ 2 * Real.pi * |τ| * |a - b| := by
  have h := abs_cos_sub_abs (2 * Real.pi * τ * a) (2 * Real.pi * τ * b)
  have habs : |2 * Real.pi * τ * a - 2 * Real.pi * τ * b|
      = 2 * Real.pi * |τ| * |a - b| := by
    rw [← mul_sub, abs_mul, abs_mul,
      abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)]
  linarith

/-- `∫_1^{1+m/K} cos(2πτy) dy = ∑_{l<m} ∫_{1+l/K}^{1+(l+1)/K} cos(2πτy) dy`. -/
theorem integral_cos_eq_sum (K : ℕ) (hK : 0 < K) (τ : ℝ) :
    ∀ m : ℕ, m ≤ K →
      ∫ y in (1 : ℝ)..(1 + (m : ℝ) / (K : ℝ)), Real.cos (2 * Real.pi * τ * y)
        = ∑ l ∈ range m,
          ∫ y in (1 + (l : ℝ) / (K : ℝ))..(1 + ((l + 1 : ℕ) : ℝ) / (K : ℝ)),
            Real.cos (2 * Real.pi * τ * y) := by
  intro m hm
  induction m with
  | zero => simp
  | succ m ih =>
    have hle : m ≤ K := by omega
    have h1 := ih hle
    have hcont : Continuous fun y : ℝ => Real.cos (2 * Real.pi * τ * y) := by fun_prop
    have hInt : ∀ a b : ℝ, IntervalIntegrable (fun y : ℝ => Real.cos (2 * Real.pi * τ * y))
        volume a b := fun a b => hcont.intervalIntegrable a b
    have hsplit : ∫ y in (1 : ℝ)..(1 + ((m + 1 : ℕ) : ℝ) / (K : ℝ)),
          Real.cos (2 * Real.pi * τ * y)
        = (∫ y in (1 : ℝ)..(1 + (m : ℝ) / (K : ℝ)), Real.cos (2 * Real.pi * τ * y))
          + ∫ y in (1 + (m : ℝ) / (K : ℝ))..(1 + ((m + 1 : ℕ) : ℝ) / (K : ℝ)),
            Real.cos (2 * Real.pi * τ * y) := by
      have hcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
      rw [hcast]
      exact (intervalIntegral.integral_add_adjacent_intervals (hInt _ _) (hInt _ _)).symm
    rw [hsplit, h1, Finset.sum_range_succ]


/-- The left-endpoint sampling error on one interval:
`|(1/K)·cos(2πτa_l) − ∫_{I_l} cos| ≤ 2π|τ|/K²`. -/
theorem abs_endpoint_error (K : ℕ) (hK : 0 < K) (τ : ℝ) (l : ℕ) :
    |(1 / (K : ℝ)) * Real.cos (2 * Real.pi * τ * (1 + (l : ℝ) / (K : ℝ)))
      - ∫ y in (1 + (l : ℝ) / (K : ℝ))..(1 + ((l + 1 : ℕ) : ℝ) / (K : ℝ)),
          Real.cos (2 * Real.pi * τ * y)|
      ≤ 2 * Real.pi * |τ| / (K : ℝ) ^ 2 := by
  have hK0 : (0 : ℝ) < ((K : ℕ) : ℝ) := by exact_mod_cast hK
  have hcast : ((l + 1 : ℕ) : ℝ) = (l : ℝ) + 1 := Nat.cast_add_one l
  have hlen : (1 + ((l + 1 : ℕ) : ℝ) / (K : ℝ)) - (1 + (l : ℝ) / (K : ℝ))
      = 1 / (K : ℝ) := by
    rw [hcast, add_div]
    have : (0 : ℝ) < (K : ℝ) := hK0
    field_simp
    ring
  have hle : (1 + (l : ℝ) / (K : ℝ)) ≤ (1 + ((l + 1 : ℕ) : ℝ) / (K : ℝ)) := by
    rw [hcast, add_div]
    have : (0 : ℝ) ≤ 1 / (K : ℝ) := by positivity
    linarith
  have hcos : Continuous fun y : ℝ => Real.cos (2 * Real.pi * τ * y) := by fun_prop
  have hconst : (1 / (K : ℝ)) * Real.cos (2 * Real.pi * τ * (1 + (l : ℝ) / (K : ℝ)))
      = ∫ y in (1 + (l : ℝ) / (K : ℝ))..(1 + ((l + 1 : ℕ) : ℝ) / (K : ℝ)),
          Real.cos (2 * Real.pi * τ * (1 + (l : ℝ) / (K : ℝ))) := by
    rw [intervalIntegral.integral_const, hlen]
    simp only [smul_eq_mul]
  have hpt : ∀ y ∈ Set.Ioc (1 + (l : ℝ) / (K : ℝ)) (1 + ((l + 1 : ℕ) : ℝ) / (K : ℝ)),
      |Real.cos (2 * Real.pi * τ * (1 + (l : ℝ) / (K : ℝ)))
        - Real.cos (2 * Real.pi * τ * y)|
        ≤ 2 * Real.pi * |τ| / (K : ℝ) := by
    intro y hy
    have hge : (1 + (l : ℝ) / (K : ℝ)) ≤ y := (Set.mem_Ioc.mp hy).1.le
    have hup : y ≤ 1 + ((l + 1 : ℕ) : ℝ) / (K : ℝ) := (Set.mem_Ioc.mp hy).2
    have h2 : |(1 + (l : ℝ) / (K : ℝ)) - y| ≤ 1 / (K : ℝ) := by
      rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hge)]
      have : y - (1 + (l : ℝ) / (K : ℝ))
          ≤ (1 + ((l + 1 : ℕ) : ℝ) / (K : ℝ)) - (1 + (l : ℝ) / (K : ℝ)) := by
        linarith
      rw [hlen] at this
      exact this
    calc |Real.cos (2 * Real.pi * τ * (1 + (l : ℝ) / (K : ℝ)))
          - Real.cos (2 * Real.pi * τ * y)|
        ≤ 2 * Real.pi * |τ| * |(1 + (l : ℝ) / (K : ℝ)) - y| :=
          abs_cos_sub_le τ (1 + (l : ℝ) / (K : ℝ)) y
      _ ≤ 2 * Real.pi * |τ| * (1 / (K : ℝ)) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = 2 * Real.pi * |τ| / (K : ℝ) := by field_simp
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 1 + (l : ℝ) / (K : ℝ)) (b := 1 + ((l + 1 : ℕ) : ℝ) / (K : ℝ))
    (C := 2 * Real.pi * |τ| / (K : ℝ))
    (f := fun y : ℝ => Real.cos (2 * Real.pi * τ * (1 + (l : ℝ) / (K : ℝ)))
      - Real.cos (2 * Real.pi * τ * y))
    (fun y hy => hpt y (by
      rw [Set.uIoc_of_le hle] at hy
      exact hy))
  rw [Real.norm_eq_abs] at hnorm
  have habs : |(1 + ((l + 1 : ℕ) : ℝ) / (K : ℝ)) - (1 + (l : ℝ) / (K : ℝ))|
      = 1 / (K : ℝ) := by
    rw [abs_of_nonneg (by linarith), hlen]
  rw [habs] at hnorm
  have hmul : (2 * Real.pi * |τ| / (K : ℝ)) * (1 / (K : ℝ))
      = 2 * Real.pi * |τ| / (K : ℝ) ^ 2 := by
    field_simp
  rw [hmul] at hnorm
  rw [hconst, ← intervalIntegral.integral_sub intervalIntegrable_const (hcos.intervalIntegrable _ _)]
  exact hnorm

/-- `∫_1^{1+K/K} cos = R(τ)`, normalising the endpoint. -/
theorem integral_cos_one_add (K : ℕ) (hK : 0 < K) (τ : ℝ) :
    ∫ y in (1 : ℝ)..(1 + ((K : ℕ) : ℝ) / ((K : ℕ) : ℝ)), Real.cos (2 * Real.pi * τ * y)
      = Rfun τ := by
  have hK0 : (0 : ℝ) < ((K : ℕ) : ℝ) := by exact_mod_cast hK
  have h : (1 : ℝ) + ((K : ℕ) : ℝ) / ((K : ℕ) : ℝ) = 2 := by
    rw [div_self hK0.ne']
    norm_num
  rw [h]
  rfl

/-- `R(τ)` as the sum of the `K` interval integrals. -/
theorem Rfun_eq_sum (K : ℕ) (hK : 0 < K) (τ : ℝ) :
    Rfun τ = ∑ l ∈ range K,
      ∫ y in (1 + (l : ℝ) / (K : ℝ))..(1 + ((l + 1 : ℕ) : ℝ) / (K : ℝ)),
        Real.cos (2 * Real.pi * τ * y) := by
  rw [← integral_cos_one_add K hK τ]
  exact integral_cos_eq_sum K hK τ K (le_refl K)

/-- **`|Re D_K(τ) − R(τ)| ≤ 2πH/K`** for `|τ| ≤ H` (part 1 of `lem:continuous-kernel`). -/
theorem abs_ReDK_sub_Rfun_le {K : ℕ} (hK : 1 ≤ K) {τ H : ℝ} (hH : |τ| ≤ H) :
    |ReDK K τ - Rfun τ| ≤ 2 * Real.pi * H / (K : ℝ) := by
  have hK0 : (0 : ℝ) < ((K : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < K)
  rw [ReDK_eq, Rfun_eq_sum K (by omega) τ]
  have hsplit : (1 / (K : ℝ)) * ∑ l ∈ range K,
        Real.cos (2 * Real.pi * τ * (1 + (l : ℝ) / (K : ℝ)))
        - ∑ l ∈ range K,
          ∫ y in (1 + (l : ℝ) / (K : ℝ))..(1 + ((l + 1 : ℕ) : ℝ) / (K : ℝ)),
            Real.cos (2 * Real.pi * τ * y)
      = ∑ l ∈ range K,
          ((1 / (K : ℝ)) * Real.cos (2 * Real.pi * τ * (1 + (l : ℝ) / (K : ℝ)))
            - ∫ y in (1 + (l : ℝ) / (K : ℝ))..(1 + ((l + 1 : ℕ) : ℝ) / (K : ℝ)),
              Real.cos (2 * Real.pi * τ * y)) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  rw [hsplit]
  have hle : ∀ l ∈ range K,
      |((1 / (K : ℝ)) * Real.cos (2 * Real.pi * τ * (1 + (l : ℝ) / (K : ℝ)))
        - ∫ y in (1 + (l : ℝ) / (K : ℝ))..(1 + ((l + 1 : ℕ) : ℝ) / (K : ℝ)),
          Real.cos (2 * Real.pi * τ * y))|
        ≤ 2 * Real.pi * |τ| / (K : ℝ) ^ 2 := by
    intro l hl
    exact abs_endpoint_error K (by omega) τ l
  have hsum := Finset.abs_sum_le_sum_abs
    (fun l : ℕ => (1 / (K : ℝ)) * Real.cos (2 * Real.pi * τ * (1 + (l : ℝ) / (K : ℝ)))
      - ∫ y in (1 + (l : ℝ) / (K : ℝ))..(1 + ((l + 1 : ℕ) : ℝ) / (K : ℝ)),
        Real.cos (2 * Real.pi * τ * y)) (range K)
  have hsum2 : ∑ l ∈ range K,
      |((1 / (K : ℝ)) * Real.cos (2 * Real.pi * τ * (1 + (l : ℝ) / (K : ℝ)))
        - ∫ y in (1 + (l : ℝ) / (K : ℝ))..(1 + ((l + 1 : ℕ) : ℝ) / (K : ℝ)),
          Real.cos (2 * Real.pi * τ * y))|
      ≤ ∑ _l ∈ range K, 2 * Real.pi * |τ| / (K : ℝ) ^ 2 :=
    Finset.sum_le_sum hle
  have hconst : ∑ _l ∈ range K, 2 * Real.pi * |τ| / (K : ℝ) ^ 2
      = 2 * Real.pi * |τ| / (K : ℝ) := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp
  have hτ : 2 * Real.pi * |τ| / (K : ℝ) ≤ 2 * Real.pi * H / (K : ℝ) := by
    apply div_le_div_of_nonneg_right _ (le_of_lt hK0)
    exact mul_le_mul_of_nonneg_left hH (by positivity)
  have hfin := hsum.trans (hsum2.trans (le_of_eq hconst))
  linarith [hfin, hτ]


/-- **`lem:continuous-kernel` (conclusion)**: for `t, s ∈ W_{K,u}` with `|t−s| ≤ H`,
`|κ_K(t,s) − R(t−s)| ≤ (2πH + 8)/K`. -/
theorem continuous_kernel {K : ℕ} (hK : 4 ≤ K) {u t s H : ℝ} (hu : 3 / 50 ≤ u)
    (ht : |t - (K : ℝ) / 4| ≤ (K : ℝ) / (100 * u))
    (hs : |s - (K : ℝ) / 4| ≤ (K : ℝ) / (100 * u))
    (hH : |t - s| ≤ H) :
    |kappa K t s - Rfun (t - s)| ≤ (2 * Real.pi * H + 8) / (K : ℝ) := by
  have h1 := finite_kernel hK hu ht hs
  have h2 := abs_ReDK_sub_Rfun_le (by omega : 1 ≤ K) hH
  have htri : |kappa K t s - Rfun (t - s)|
      ≤ |kappa K t s - ReDK K (t - s)| + |ReDK K (t - s) - Rfun (t - s)| := by
    have := abs_add_le (kappa K t s - ReDK K (t - s)) (ReDK K (t - s) - Rfun (t - s))
    ring_nf at this
    exact this
  have hgoal : |kappa K t s - Rfun (t - s)|
      ≤ 8 / (K : ℝ) + 2 * Real.pi * H / (K : ℝ) := by
    linarith [h1, h2, htri]
  have hsum : 8 / (K : ℝ) + 2 * Real.pi * H / (K : ℝ)
      = (2 * Real.pi * H + 8) / (K : ℝ) := by
    field_simp
    ring
  rw [← hsum]
  exact hgoal

end RudinDensity
end CenteredCube

#print axioms CenteredCube.RudinDensity.abs_cos_sub_abs
#print axioms CenteredCube.RudinDensity.abs_cos_sub_le
#print axioms CenteredCube.RudinDensity.integral_cos_eq_sum
#print axioms CenteredCube.RudinDensity.abs_endpoint_error
#print axioms CenteredCube.RudinDensity.Rfun_eq_sum
#print axioms CenteredCube.RudinDensity.abs_ReDK_sub_Rfun_le
#print axioms CenteredCube.RudinDensity.continuous_kernel
