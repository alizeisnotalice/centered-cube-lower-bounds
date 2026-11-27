import Mathlib.Data.Int.Interval
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace CenteredCubeSqrt

/-- Pull a physical window of half-width C/(Kv) back to the integer
difference lattice. The lattice width is independent of the dimension. -/
theorem local_fine_window_pullback {B K v C x : ℝ} (hB : 0 < B) (hK : 0 < K)
    (hv : 0 < v) (hC : 0 ≤ C) (hBv : B ≤ 2*v) (ell : ℤ)
    (h : |(ell:ℝ)/(B*K)-x| ≤ C/(K*v)) :
    |(ell:ℝ)-B*K*x| ≤ 2*C := by
  have hden : 0 < B*K := by positivity
  have left : (ell:ℝ)-B*K*x = ((ell:ℝ)/(B*K)-x)*(B*K) := by
    field_simp
  rw [left,abs_mul,abs_of_pos hden]
  have hi := mul_le_mul_of_nonneg_right h hden.le
  have e : C/(K*v)*(B*K) = C*(B/v) := by field_simp
  rw [e] at hi
  have hb : B/v ≤ 2 := (div_le_iff₀ hv).mpr (by linarith)
  exact hi.trans (by simpa [mul_comm] using mul_le_mul_of_nonneg_left hb hC)

/-- A padded interval of at most 2D+1 difference-grid points, valid
uniformly in the window center. -/
theorem local_fine_window_contained {x C : ℝ} {D : ℕ} (hD : 2*C+1 ≤ D)
    {ell : ℤ} (h : |(ell:ℝ)-x| ≤ 2*C) :
    ell ∈ Finset.Icc (⌊x⌋-(D:ℤ)) (⌊x⌋+D) := by
  rcases abs_le.mp h with ⟨hl,hr⟩
  have hfloor := Int.floor_le x
  have hceil := Int.lt_floor_add_one x
  apply Finset.mem_Icc.mpr
  constructor
  · exact_mod_cast (show (⌊x⌋:ℝ)-(D:ℝ) ≤ ell by linarith)
  · exact_mod_cast (show (ell:ℝ) ≤ (⌊x⌋:ℝ)+D by linarith)

theorem padded_integer_window_card (x : ℝ) (D : ℕ) :
    (Finset.Icc (⌊x⌋-(D:ℤ)) (⌊x⌋+D)).card = 2*D+1 := by
  rw [Int.card_Icc]
  have he : ⌊x⌋+(D:ℤ)+1-(⌊x⌋-(D:ℤ)) = ((2*D+1:ℕ):ℤ) := by push_cast; ring
  rw [he,Int.toNat_natCast]

/-- The mirror window at length (L_0) has two coarse carry candidates.
Each is within strictly two of the safe baseline for large enough v. -/
theorem local_both_mirror_carries_near {B K v C L : ℝ}
    (hB : 0 < B) (hK : 0 < K) (hv : 0 < v)
    (hC : 0 ≤ C ∧ C < v) {ell k : ℤ} {r : ℝ}
    (hr : 0 ≤ r ∧ r < B) (he : (ell:ℝ)=B*(k:ℝ)+r)
    (hwin : |(ell:ℝ)/(B*K)-L| ≤ C/(K*v)) :
    |(k:ℝ)-K*L| < 2 ∧ |(k:ℝ)+1-K*L| < 2 := by
  have hfin : |(ell:ℝ)/B-K*L| < 1 := by
    have e : (ell:ℝ)/B-K*L = ((ell:ℝ)/(B*K)-L)*K := by field_simp
    rw [e,abs_mul,abs_of_pos hK]
    apply (mul_le_mul_of_nonneg_right hwin hK.le).trans_lt
    have e : C/(K*v)*K = C/v := by field_simp
    rw [e]
    exact (div_lt_one hv).mpr hC.2
  have hf : (ell:ℝ)/B = (k:ℝ)+r/B := by rw [he]; field_simp
  rw [hf] at hfin
  have hflo := abs_lt.mp hfin
  have hrl : 0 ≤ r/B := div_nonneg hr.1 hB.le
  have hrh : r/B < 1 := (div_lt_one hB).mpr hr.2
  exact ⟨abs_lt.mpr ⟨by linarith [hflo.1],by linarith [hflo.2]⟩,
    abs_lt.mpr ⟨by linarith [hflo.1],by linarith [hflo.2]⟩⟩

/-- Near a single boundary, every nonzero difference in the local
window is strictly smaller than one coarse atom bin. -/
theorem local_same_direction_small {B K v C : ℝ}
    (hB : 0 < B) (hK : 0 < K) (hv : 0 < v) (hC : C < v)
    {ell : ℤ} (hwin : |(ell:ℝ)/(B*K)| ≤ C/(K*v)) :
    |(ell:ℝ)| < B := by
  have hs : 0 < B*K := by positivity
  rw [abs_div,abs_of_pos hs] at hwin
  have h := (div_le_iff₀ hs).mp hwin
  have e : C/(K*v)*(B*K)=B*(C/v) := by field_simp
  rw [e] at h
  exact h.trans_lt (by
    have h1 := mul_lt_mul_of_pos_left ((div_lt_one hv).mpr hC) hB
    simpa using h1)

#print axioms local_fine_window_pullback
#print axioms padded_integer_window_card
#print axioms local_both_mirror_carries_near
#print axioms local_same_direction_small

end CenteredCubeSqrt
