import SqrtActualNearNormalized

namespace CenteredCubeSqrt
open Set MeasureTheory
open scoped BigOperators Interval
set_option maxHeartbeats 750000

theorem real_floor_nonzero_mod_pair {K : ℕ} [NeZero K] {x : ℝ} (h1 : 1≤x)
    (h2 : x<(K:ℝ)-1) :
    let k : ℤ := ⌊x⌋
    (k:ZMod K) ≠ 0 ∧ ((k+1:ℤ):ZMod K) ≠ 0 := by
  let k : ℤ := ⌊x⌋
  have lo : (1:ℤ)≤k := Int.le_floor.mpr (by exact_mod_cast h1)
  have hi : k+1<(K:ℤ) := by
    have hk := Int.floor_le x
    exact_mod_cast (show (k:ℝ)+1<(K:ℝ) by linarith)
  have one (j : ℤ) (jl : 0<j) (jh : j<(K:ℤ)) : (j:ZMod K) ≠0 := by
    intro h
    have H := (ZMod.intCast_zmod_eq_zero_iff_dvd j K).mp h
    have J := Int.le_of_dvd jl H
    omega
  exact ⟨one k (by omega) (by omega),one (k+1) (by omega) hi⟩

theorem actual_far_nonzero_carries {K : ℕ} [NeZero K] (hK : 18≤K) {L J : ℝ}
    (hL : L∈Icc (10/9:ℝ) (11/9)) (hJ : J∈Icc (10/9:ℝ) (11/9))
    (hτ : 1≤(K:ℝ)*(J-L)/2) :
    let τ := (K:ℝ)*(J-L)/2
    let s := (K:ℝ)*((L+J)/2-1)
    (((⌊τ⌋:ℤ):ZMod K) ≠0 ∧ (((⌊τ⌋:ℤ)+1:ℤ):ZMod K) ≠0) ∧
    (((⌊s⌋:ℤ):ZMod K) ≠0 ∧ (((⌊s⌋:ℤ)+1:ℤ):ZMod K) ≠0) := by
  let τ := (K:ℝ)*(J-L)/2
  let s := (K:ℝ)*((L+J)/2-1)
  have hKr : 18≤(K:ℝ) := by exact_mod_cast hK
  have h₀ : τ≤(K:ℝ)/18 := by
    dsimp [τ]
    linarith [mul_le_mul_of_nonneg_left (show J-L≤1/9 by linarith [hL.1,hJ.2])
      (show 0≤(K:ℝ) by positivity)]
  have h₁ : (K:ℝ)/9≤s := by
    dsimp [s]
    linarith [mul_le_mul_of_nonneg_left (show (1:ℝ)/9≤(L+J)/2-1 by linarith [hL.1,hJ.1])
      (show 0≤(K:ℝ) by positivity)]
  have h₂ : s≤2*(K:ℝ)/9 := by
    dsimp [s]
    linarith [mul_le_mul_of_nonneg_left (show (L+J)/2-1≤(2:ℝ)/9 by linarith [hL.2,hJ.2])
      (show 0≤(K:ℝ) by positivity)]
  have hτa : 1≤τ := hτ
  have hτb : τ<(K:ℝ)-1 := by linarith
  have hsa : 1≤s := by linarith
  have hsb : s<(K:ℝ)-1 := by linarith
  exact ⟨real_floor_nonzero_mod_pair hτa hτb,real_floor_nonzero_mod_pair hsa hsb⟩

theorem rawCorrelation_period_shift {B K : ℕ} [NeZero K] (f : ZMod K→Fin B) (z : ℝ) :
    rawCorrelation f (z+(K:ℝ))=rawCorrelation f z := by
  have hK : (K:ℝ)≠0 := by exact_mod_cast NeZero.ne K
  unfold rawCorrelation
  simp only [add_div,div_self hK,←add_assoc,actualRawPrimitive_periodic f _]

theorem actualRaw_far_covariance_from_nonzero {B K : ℕ} [NeZero K] (f : ZMod K→Fin B)
    (hK : 18≤K) {L J Q : ℝ}
    (hL : L∈Icc (10/9:ℝ) (11/9)) (hJ : J∈Icc (10/9:ℝ) (11/9))
    (hτ : 1≤(K:ℝ)*(J-L)/2)
    (hC : ∀ z : ℝ, ((⌊z⌋:ℤ):ZMod K) ≠0 → (((⌊z⌋:ℤ)+1:ℤ):ZMod K) ≠0 →
      |rawCorrelation f z|≤Q) :
    |periodInner (actualRawWindow f L) (actualRawWindow f J)|≤4*Q := by
  let τ := (K:ℝ)*(J-L)/2
  let s := (K:ℝ)*((L+J)/2-1)
  obtain ⟨⟨h1,h2⟩,⟨h3,h4⟩⟩ := actual_far_nonzero_carries hK hL hJ hτ
  have A := hC τ h1 h2
  have B := hC s h3 h4
  rw [rawWindow_covariance_from_correlation f L J,
    show (K:ℝ)*(J+L)/2=s+(K:ℝ) by dsimp [s]; ring,rawCorrelation_period_shift]
  change |2*rawCorrelation f τ-2*rawCorrelation f s|≤_
  have u := abs_add_le (2*rawCorrelation f τ) (-(2*rawCorrelation f s))
  rw [←sub_eq_add_neg,abs_neg,abs_mul,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤2)] at u
  exact u.trans (by linarith)

#print axioms actualRaw_far_covariance_from_nonzero
#print axioms actual_far_nonzero_carries
end CenteredCubeSqrt
