import GridTelescoping

open Filter Set
open scoped NNReal Topology
namespace CubeBrownian

noncomputable def dyadicT (T : ℝ≥0) (r k : ℕ) : ℝ≥0 := T * k / (2:ℝ≥0)^r

theorem dyadicT_zero (T : ℝ≥0) (r : ℕ) : dyadicT T r 0 = 0 := by simp [dyadicT]

theorem dyadicT_last (T : ℝ≥0) (r : ℕ) : dyadicT T r (2^r) = T := by
  simp [dyadicT, pow_ne_zero _ (by norm_num : (2:ℝ≥0) ≠ 0)]

theorem dyadicT_mono (T : ℝ≥0) (r : ℕ) : Monotone (dyadicT T r) := by
  intro i j hij
  unfold dyadicT
  gcongr

theorem dyadicT_refine (T : ℝ≥0) (r k : ℕ) :
    dyadicT T (r+1) (2*k) = dyadicT T r k := by
  apply NNReal.eq
  push_cast [dyadicT,pow_succ]
  field_simp

theorem dyadicT_succ_sub (T : ℝ≥0) (r k : ℕ) :
    (dyadicT T r (k+1):ℝ) -(dyadicT T r k:ℝ) = (T:ℝ) / (2:ℝ)^r := by
  push_cast [dyadicT]
  ring

theorem dyadic_step_tendsto (T : ℝ≥0) :
    Tendsto (fun r : ℕ ↦ (T:ℝ) / (2:ℝ)^r) atTop (𝓝 0) := by
  simpa only [div_eq_mul_inv, ← inv_pow, mul_zero] using
    (tendsto_const_nhds (x := (T:ℝ))).mul
      (tendsto_pow_atTop_nhds_zero_of_abs_lt_one (by norm_num : |(2:ℝ)⁻¹| < 1))

noncomputable def dyadicBelowIndex (T s : ℝ≥0) (r : ℕ) : ℕ :=
  ⌊(s:ℝ) * (2:ℝ)^r / (T:ℝ)⌋₊

theorem dyadicBelowIndex_le {T s : ℝ≥0} (hT : 0 < T) (hs : s ≤ T) (r : ℕ) :
    dyadicBelowIndex T s r ≤ 2^r := by
  have hTP : 0 < (T:ℝ) := by exact_mod_cast hT
  have hsR : (s:ℝ) ≤ (T:ℝ) := by exact_mod_cast hs
  apply Nat.floor_le_of_le
  push_cast
  apply (div_le_iff₀ hTP).2
  rw [mul_comm ((2:ℝ)^r)]
  gcongr

theorem dyadicBelow_tendsto {T s : ℝ≥0} (hT : 0 < T) :
    Tendsto (fun r ↦ dyadicT T r (dyadicBelowIndex T s r)) atTop (𝓝 s) := by
  have hTP : 0 < (T:ℝ) := by exact_mod_cast hT
  rw [← NNReal.tendsto_coe, tendsto_iff_dist_tendsto_zero]
  apply squeeze_zero (fun _ ↦ dist_nonneg) _ (dyadic_step_tendsto T)
  intro r
  have hd : 0 < (2:ℝ)^r := by positivity
  let u : ℝ := (s:ℝ) * (2:ℝ)^r / (T:ℝ)
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have h₁ := (le_div_iff₀ hTP).mp (Nat.floor_le hu)
  have h₂ := (div_lt_iff₀ hTP).mp (Nat.lt_floor_add_one u)
  have hL : (dyadicT T r (dyadicBelowIndex T s r):ℝ) ≤ (s:ℝ) := by
    push_cast [dyadicT,dyadicBelowIndex]
    apply (div_le_iff₀ hd).2
    nlinarith only [h₁]
  rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hL), neg_sub]
  rw [sub_le_iff_le_add]
  push_cast [dyadicT,dyadicBelowIndex]
  rw [← add_div]
  apply (le_div_iff₀ hd).2
  dsimp [u] at h₂
  nlinarith only [h₂]

end CubeBrownian
#print axioms CubeBrownian.dyadicBelow_tendsto
