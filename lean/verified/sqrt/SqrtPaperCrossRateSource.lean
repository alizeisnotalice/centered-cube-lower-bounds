import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

open scoped Topology BigOperators
open Filter
namespace CubeSqrtEnd

theorem scale_sq_div_sqrt_tendsto {v K : ℕ → ℝ}
    (hv : ∀ᶠ n in atTop, 0 ≤ v n)
    (h : Tendsto (fun n => K n / (v n)^4) atTop atTop) :
    Tendsto (fun n => (v n)^2 / Real.sqrt (K n)) atTop (𝓝 0) := by
  have hpos : ∀ᶠ n in atTop, 0 < K n / (v n)^4 :=
    (tendsto_atTop.1 h 1).mono fun _ hn => lt_of_lt_of_le (by norm_num) hn
  have hi : Tendsto (fun n => (Real.sqrt (K n / (v n)^4))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp h)
  apply hi.congr'
  filter_upwards [hv, hpos] with n hnv hn
  have hvne : v n ≠ 0 := by intro he; simp [he] at hn
  have hs : Real.sqrt ((v n)^4) = (v n)^2 := by
    rw [show (v n)^4 = ((v n)^2)^2 by ring, Real.sqrt_sq (sq_nonneg _)]
  rw [Real.sqrt_div' _ (by positivity), hs, inv_div]

noncomputable def coarsePaperCross (a K : ℝ) (M : ℕ) : ℝ :=
  (40 / 9) * (a * Real.sqrt (K+1) / K *
    (∑ m ∈ Finset.Icc 1 M, ((m : ℝ)^2)⁻¹) +
    Real.pi * a^2 / (2*K) * (∑ m ∈ Finset.Icc 1 M, (m : ℝ)⁻¹))

theorem coarsePaperCross_nonneg {a K : ℝ} (ha : 0 ≤ a) (hK : 0 < K) (M : ℕ) :
    0 ≤ coarsePaperCross a K M := by
  unfold coarsePaperCross
  positivity

theorem coarsePaperCross_le {a K : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hK : 1 ≤ K) (M : ℕ) :
    coarsePaperCross a K M ≤ (160 / 9) * (M : ℝ) / Real.sqrt K := by
  have hk : 0 < K := by linarith
  have hs : 0 < Real.sqrt K := Real.sqrt_pos.2 hk
  have hs1 : 1 ≤ Real.sqrt K := (Real.le_sqrt (by norm_num : (0:ℝ) ≤ 1) hk.le).2 (by simpa using hK)
  have hsK : Real.sqrt K ≤ K := by nlinarith [Real.sq_sqrt hk.le]
  have hc1 : a * Real.sqrt (K+1) / K ≤ 2 / Real.sqrt K := by
    have hr : Real.sqrt (K+1) ≤ 2 * Real.sqrt K := by
      nlinarith [Real.sq_sqrt (show 0 ≤ K+1 by linarith), Real.sq_sqrt hk.le,
        Real.sqrt_nonneg (K+1)]
    have hr' : a * Real.sqrt (K+1) ≤ 2 * Real.sqrt K := by
      have he : a * Real.sqrt (K+1) ≤ Real.sqrt (K+1) := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right ha1 (Real.sqrt_nonneg (K+1))
      exact he.trans hr
    rw [div_le_div_iff₀ hk hs]
    calc
      a * Real.sqrt (K+1) * Real.sqrt K ≤ (2 * Real.sqrt K) * Real.sqrt K :=
        mul_le_mul_of_nonneg_right hr' hs.le
      _ = 2 * K := by rw [mul_assoc, Real.mul_self_sqrt hk.le]
  have hc2 : Real.pi * a^2 / (2*K) ≤ 2 / Real.sqrt K := by
    have hp : Real.pi ≤ 4 := le_of_lt (Real.pi_lt_d20.trans (by norm_num))
    have ha2 : a^2 ≤ 1 := by nlinarith [mul_nonneg ha (sub_nonneg.2 ha1)]
    have hpa : Real.pi * a^2 ≤ 4 :=
      (mul_le_mul_of_nonneg_left ha2 Real.pi_pos.le).trans (by simpa using hp)
    rw [div_le_div_iff₀ (by positivity : 0 < 2*K) hs]
    calc
      Real.pi * a^2 * Real.sqrt K ≤ 4 * Real.sqrt K :=
        mul_le_mul_of_nonneg_right hpa hs.le
      _ ≤ 2 * (2 * K) := by linarith
  have hsum (j : ℕ) (hj : j = 1 ∨ j = 2) :
      (∑ m ∈ Finset.Icc 1 M, ((m : ℝ)^j)⁻¹) ≤ (M : ℝ) := by
    have hc : (Finset.Icc 1 M).card = M := by simp [Nat.card_Icc]
    calc
      _ ≤ ∑ _m ∈ Finset.Icc 1 M, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro m hm
        have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Icc.1 hm).1
        have hmj : 1 ≤ (m : ℝ)^j := one_le_pow₀ hm1
        exact inv_le_one_of_one_le₀ hmj
      _ = (M : ℝ) := by simp [hc]
  have hl : (∑ m ∈ Finset.Icc 1 M, (m : ℝ)⁻¹) ≤ (M : ℝ) := by
    simpa only [pow_one] using hsum 1 (Or.inl rfl)
  have hq := hsum 2 (Or.inr rfl)
  unfold coarsePaperCross
  calc
    _ ≤ (40 / 9 : ℝ) * ((2 / Real.sqrt K) * M + (2 / Real.sqrt K) * M) := by
      gcongr
    _ = _ := by ring

theorem coarsePaperCross_scaled_tendsto {a K v : ℕ → ℝ} {M : ℕ → ℕ}
    (ha : ∀ᶠ n in atTop, 0 ≤ a n ∧ a n ≤ 1)
    (hK : ∀ᶠ n in atTop, 1 ≤ K n)
    (hM : ∀ᶠ n in atTop, (M n : ℝ) ≤ v n)
    (hr : Tendsto (fun n => K n / (v n)^4) atTop atTop) :
    Tendsto (fun n => v n * coarsePaperCross (a n) (K n) (M n)) atTop (𝓝 0) := by
  have hv : ∀ᶠ n in atTop, 0 ≤ v n := hM.mono fun n hn => (Nat.cast_nonneg (M n)).trans hn
  have h := (scale_sq_div_sqrt_tendsto hv hr).const_mul (160 / 9 : ℝ)
  rw [mul_zero] at h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h ?_ ?_
  · filter_upwards [ha, hK, hv] with n han hkn hvn
    have hc := coarsePaperCross_nonneg (a := a n) (K := K n) han.1 (by linarith) (M n)
    exact mul_nonneg hvn hc
  · filter_upwards [ha, hK, hM, hv] with n han hkn hmn hvn
    have hc := coarsePaperCross_le han.1 han.2 hkn (M n)
    calc
      _ ≤ v n * ((160 / 9 : ℝ) * (M n : ℝ) / Real.sqrt (K n)) :=
        mul_le_mul_of_nonneg_left hc hvn
      _ ≤ v n * ((160 / 9 : ℝ) * v n / Real.sqrt (K n)) := by gcongr
      _ = _ := by ring

theorem coarsePaperCross_with_smoothing_tendsto {a K v : ℕ → ℝ} {M : ℕ → ℕ}
    {w : ℝ} (hw : 0 < w)
    (ha : ∀ᶠ n in atTop, 0 ≤ a n ∧ a n ≤ 1)
    (hK : ∀ᶠ n in atTop, 1 ≤ K n)
    (hv : ∀ᶠ n in atTop, 0 < v n)
    (hM : ∀ᶠ n in atTop, (M n : ℝ) ≤ v n)
    (hr : Tendsto (fun n => K n / (v n)^4) atTop atTop) :
    Tendsto (fun n => v n * (coarsePaperCross (a n) (K n) (M n) +
        2 / (3 * w * v n))) atTop (𝓝 (2 / (3 * w))) := by
  have ht := coarsePaperCross_scaled_tendsto ha hK hM hr
  have hconst : Tendsto (fun _ : ℕ => 2 / (3 * w)) atTop (𝓝 (2 / (3 * w))) :=
    tendsto_const_nhds
  have hsum : Tendsto (fun n => v n * coarsePaperCross (a n) (K n) (M n) +
      2 / (3 * w)) atTop (𝓝 (2 / (3 * w))) := by
    simpa only [zero_add] using ht.add hconst
  refine hsum.congr' ?_
  filter_upwards [hv] with n hvn
  have he : v n * (2 / (3 * w * v n)) = 2 / (3 * w) := by
    field_simp [ne_of_gt hw, ne_of_gt hvn]
  rw [mul_add, he]

#print axioms coarsePaperCross_with_smoothing_tendsto

#print axioms scale_sq_div_sqrt_tendsto
#print axioms coarsePaperCross_le
#print axioms coarsePaperCross_scaled_tendsto
end CubeSqrtEnd
