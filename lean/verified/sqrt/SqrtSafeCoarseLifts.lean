import SqrtCyclicSafety
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace CenteredCubeSqrt

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- Lifted form of continuous safety: every integer lift of each genuine
defect residue is separated by more than two coarse cells. -/
def actualSafeLifts {b d : ℕ} (hd : 0<d) (g : (LabelField d)ˣ)
    (hg : orderOf g=2^d-1) (t : Fin b → LabelField d) (L : ℝ) : Prop :=
  ∀ k : ℤ, (k:ZMod (2^d-1)) ∈ cyclicDefects hd g hg t →
    2 < |(k:ℝ)-(((2^d-1:ℕ):ℝ))*(L-1)|

theorem phaseState_eq_one_iff_zero {d : ℕ} (hd : 0<d) (g : (LabelField d)ˣ)
    (hg : orderOf g=2^d-1) (r : ZMod (2^d-1)) :
    (phaseState hd g hg r : LabelField d)=1 ↔ r=0 := by
  have he : phaseState hd g hg 0=1 := map_one (cyclicStateEquiv hd g hg)
  constructor
  · intro h
    have hh : phaseState hd g hg r = phaseState hd g hg 0 := by
      rw [he]
      exact Units.ext h
    exact congrArg Multiplicative.toAdd ((cyclicStateEquiv hd g hg).injective hh)
  · rintro rfl
    rw [he,Units.val_one]

/-- Both nominal mirror carries from the support bound are regular:
the geometric interval excludes zero, and the actual safe lift excludes
the genuine finite-field defect ratios. -/
theorem actualSafeLifts_regular_coarse {b d : ℕ} (hd : 0<d) (g : (LabelField d)ˣ)
    (hg : orderOf g=2^d-1) {t : Fin b → LabelField d} {L : ℝ}
    (hK : 18≤(2^d-1:ℕ))
    (hL : 10/9≤L ∧ L≤11/9)
    (hSafe : actualSafeLifts hd g hg t L) (k : ℤ)
    (hne : |(k:ℝ)-(((2^d-1:ℕ):ℝ))*L|<2) :
    (phaseState hd g hg (k:ZMod (2^d-1)) : LabelField d) ≠ 1 ∧
    (phaseState hd g hg (k:ZMod (2^d-1)) : LabelField d) ∉ labelRatioSet t := by
  let K : ℕ := 2^d-1
  have hKr : (18:ℝ) ≤ K := by exact_mod_cast hK
  have hKp : 0 < (K:ℝ) := by linarith
  constructor
  · intro h
    have h0 : (k:ZMod K)=0 := (phaseState_eq_one_iff_zero hd g hg _).mp h
    have e : (0:ℤ) ≡ k [ZMOD (K:ℤ)] := by
      apply Int.modEq_iff_dvd.mpr
      rw [← ZMod.intCast_eq_intCast_iff_dvd_sub]
      simpa only [Int.cast_zero] using h0.symm
    obtain ⟨q,hq⟩ := Int.modEq_iff_add_fac.mp e
    have hqr : (k:ℝ) = (K:ℝ)*(q:ℝ) := by exact_mod_cast (by simpa only [zero_add] using hq : k = (K:ℤ)*q)
    have hnear := abs_lt.mp hne
    change -(2:ℝ)<(k:ℝ)-(K:ℝ)*L ∧ (k:ℝ)-(K:ℝ)*L<2 at hnear
    rcases (show q≤1 ∨ 2≤q by omega) with hq1 | hq2
    · have hqr1 : (q:ℝ) ≤ 1 := by exact_mod_cast hq1
      have hh := mul_le_mul_of_nonneg_left (show (q:ℝ)-L ≤ -(1:ℝ)/9 by linarith [hL.1]) hKp.le
      nlinarith [hnear.1]
    · have hqr2 : (2:ℝ) ≤ q := by exact_mod_cast hq2
      have hh := mul_le_mul_of_nonneg_left (show (1:ℝ)/9 ≤ (q:ℝ)-L by linarith [hL.2]) hKp.le
      nlinarith [hnear.2]
  · intro h
    have hD : ((k-(K:ℤ):ℤ):ZMod K) ∈ cyclicDefects hd g hg t := by
      have e : ((k-(K:ℤ):ℤ):ZMod K) = (k:ZMod K) := by simp
      rw [e]
      exact h
    have hlt := hSafe (k-(K:ℤ)) hD
    change 2 < |((k-(K:ℤ):ℤ):ℝ)-(K:ℝ)*(L-1)| at hlt
    push_cast at hlt
    rw [show (k:ℝ)-(K:ℝ)-(K:ℝ)*(L-1)=(k:ℝ)-(K:ℝ)*L by ring] at hlt
    exact (not_lt_of_ge hne.le) hlt

#print axioms actualSafeLifts_regular_coarse

end CenteredCubeSqrt
