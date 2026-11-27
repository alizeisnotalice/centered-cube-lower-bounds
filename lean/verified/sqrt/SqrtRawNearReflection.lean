import SqrtRawNearBound
import SqrtActualRawSafeDiagonal

namespace CenteredCubeSqrt
open MeasureTheory Set
open scoped Interval BigOperators
set_option maxHeartbeats 1000000
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem actualSafe_reflection_carry_regular {b d : ℕ} (hd : 0<d)
    (g : (LabelField d)ˣ) (hg : orderOf g=2^d-1) {t : Fin b→LabelField d}
    {L J : ℝ} (hK : 18≤(2^d-1:ℕ))
    (hM : (L+J)/2∈Icc (10/9:ℝ) (11/9))
    (hs : actualSafeLifts hd g hg t L) {k : ℤ}
    (hτ : (((2^d-1:ℕ):ℝ))*(J-L)/2∈Icc (0:ℝ) 1)
    (hne : |(k:ℝ)-(((2^d-1:ℕ):ℝ))*((L+J)/2)|≤1) :
    (phaseState hd g hg (k:ZMod (2^d-1)) : LabelField d) ≠ 1 ∧
    (phaseState hd g hg (k:ZMod (2^d-1)) : LabelField d) ∉ labelRatioSet t := by
  let K : ℕ := 2^d-1
  let M := (L+J)/2
  have hKr : (18:ℝ)≤K := by exact_mod_cast hK
  have hKp : 0<(K:ℝ) := by linarith
  have hnear : -(1:ℝ)≤(k:ℝ)-(K:ℝ)*M ∧ (k:ℝ)-(K:ℝ)*M≤1 := abs_le.mp hne
  have hM' : M∈Icc (10/9:ℝ) (11/9) := hM
  constructor
  · intro h
    have h0 : (k:ZMod K)=0 := (phaseState_eq_one_iff_zero hd g hg _).mp h
    have e : (0:ℤ) ≡ k [ZMOD (K:ℤ)] := by
      apply Int.modEq_iff_dvd.mpr
      rw [←ZMod.intCast_eq_intCast_iff_dvd_sub]
      simpa only [Int.cast_zero] using h0.symm
    obtain ⟨q,hq⟩ := Int.modEq_iff_add_fac.mp e
    have hqr : (k:ℝ)=(K:ℝ)*(q:ℝ) := by exact_mod_cast (by simpa only [zero_add] using hq : k=(K:ℤ)*q)
    rcases (show q≤1 ∨ 2≤q by omega) with hq1|hq2
    · have hq1' : (q:ℝ)≤1 := by exact_mod_cast hq1
      have hh := mul_le_mul_of_nonneg_left (show (q:ℝ)-M≤-(1:ℝ)/9 by linarith [hM'.1]) hKp.le
      nlinarith [hnear.1]
    · have hq2' : (2:ℝ)≤q := by exact_mod_cast hq2
      have hh := mul_le_mul_of_nonneg_left (show (1:ℝ)/9≤(q:ℝ)-M by linarith [hM'.2]) hKp.le
      nlinarith [hnear.2]
  · intro h
    have hD : ((k-(K:ℤ):ℤ):ZMod K) ∈ cyclicDefects hd g hg t := by
      have e : ((k-(K:ℤ):ℤ):ZMod K)=(k:ZMod K) := by simp
      rw [e]
      exact h
    have E := hs (k-(K:ℤ)) hD
    change 2 < |((k-(K:ℤ):ℤ):ℝ)-(K:ℝ)*(L-1)| at E
    push_cast at E
    rw [show (k:ℝ)-(K:ℝ)-(K:ℝ)*(L-1)=((k:ℝ)-(K:ℝ)*M)+(K:ℝ)*(J-L)/2 by unfold M; ring] at E
    have T : |(K:ℝ)*(J-L)/2|≤1 :=
      by rw [abs_of_nonneg hτ.1]; exact hτ.2
    exact (not_lt_of_ge ((abs_add_le _ _).trans (by linarith [add_le_add hne T]))) E

theorem actual_raw_near_reflected_correlation_bound {b d : ℕ} [NeZero (2^d-1)]
    (hd : 0<d) (g : (LabelField d)ˣ) (hg : orderOf g=2^d-1) {t : Fin b → LabelField d}
    (ht : LinearIndependent (ZMod 2) t) (hdim : 2*b≤d)
    {L J : ℝ} (hK : 18≤(2^d-1:ℕ)) (hL : L∈Icc (10/9:ℝ) (11/9)) (hJ : J∈Icc (10/9:ℝ) (11/9))
    (hSafe : actualSafeLifts hd g hg t L)
    (hτ : (((2^d-1:ℕ):ℝ))*(J-L)/2∈Icc (0:ℝ) 1) :
    let f := ordinalPhaseLabel hd g hg t
    let K := ((2^d-1:ℕ):ℝ)
    |rawCorrelation f (K*((L+J)/2))|≤1/(12*((2:ℝ)^b)^2)+1/(2*K) := by
  let f := ordinalPhaseLabel hd g hg t
  let K := ((2^d-1:ℕ):ℝ)
  let M := (L+J)/2
  let k : ℤ := ⌊K*M⌋
  let θ := K*M-(k:ℝ)
  have hM : M∈Icc (10/9:ℝ) (11/9) := ⟨by dsimp [M]; linarith [hL.1,hJ.1],
    by dsimp [M]; linarith [hL.2,hJ.2]⟩
  have hu : (k:ℝ)≤K*M := Int.floor_le _
  have hl : K*M<(k:ℝ)+1 := Int.lt_floor_add_one _
  have hθ : θ∈Icc (0:ℝ) 1 := ⟨by dsimp [θ]; linarith,by dsimp [θ]; linarith⟩
  have h1 : |(k:ℝ)-K*M|≤1 := abs_le.mpr ⟨by linarith,by linarith⟩
  have h2 : |((k+1:ℤ):ℝ)-K*M|≤1 := by push_cast; exact abs_le.mpr ⟨by linarith,by linarith⟩
  obtain ⟨e1,e2⟩ := actualSafe_reflection_carry_regular hd g hg hK hM hSafe hτ h1
  obtain ⟨e3,e4⟩ := actualSafe_reflection_carry_regular hd g hg hK hM hSafe hτ h2
  push_cast at e3 e4
  change |rawCorrelation f (K*M)| ≤ _
  rw [show K*M=(k:ℝ)+θ by dsimp [θ]; ring]
  exact actual_raw_regular_correlation_bound hd g hg ht hdim k hθ e1 e2 e3 e4

#print axioms actual_raw_near_reflected_correlation_bound
end CenteredCubeSqrt
