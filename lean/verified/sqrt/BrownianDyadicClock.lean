import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

namespace CubeBrownian
open Filter
open scoped NNReal Topology

noncomputable def dyadicClock (m k : ℕ) : ℝ≥0 := (k:ℝ≥0)/(2:ℝ≥0)^m

noncomputable def dyadicIndex (m : ℕ) (t : ℝ≥0) : ℕ :=
  ⌊(t:ℝ)*(2:ℝ)^m⌋₊

noncomputable def dyadicError (m : ℕ) : ℝ := (7/8:ℝ)^m

theorem dyadicClock_coe (m k : ℕ) :
    (dyadicClock m k : ℝ)=(k:ℝ)/(2:ℝ)^m := by
  unfold dyadicClock
  push_cast
  rfl

theorem dyadicClock_even (m k : ℕ) : dyadicClock (m+1) (2*k)=dyadicClock m k := by
  apply NNReal.eq
  rw [dyadicClock_coe,dyadicClock_coe,Nat.cast_mul,pow_succ]
  push_cast
  ring

theorem dyadicClock_adjacent_dist (m k : ℕ) :
    dist (dyadicClock m (k+1)) (dyadicClock m k) = (1:ℝ)/(2:ℝ)^m := by
  change dist ((dyadicClock m (k+1):ℝ)) ((dyadicClock m k:ℝ)) = _
  rw [Real.dist_eq,dyadicClock_coe,dyadicClock_coe,Nat.cast_succ,←sub_div]
  ring_nf
  rw [abs_of_nonneg (by positivity)]

theorem dyadicIndex_floor_bounds (m : ℕ) (t : ℝ≥0) :
    ((dyadicIndex m t):ℝ)≤(t:ℝ)*(2:ℝ)^m ∧
       (t:ℝ)*(2:ℝ)^m<((dyadicIndex m t):ℝ)+1 := by
  unfold dyadicIndex
  exact ⟨Nat.floor_le (by positivity),Nat.lt_floor_add_one _⟩

theorem dyadicIndex_step (m : ℕ) (t : ℝ≥0) :
    dyadicIndex (m+1) t=2*dyadicIndex m t ∨
      dyadicIndex (m+1) t=2*dyadicIndex m t+1 := by
  let k := dyadicIndex m t
  have h := dyadicIndex_floor_bounds m t
  have h₂ := dyadicIndex_floor_bounds (m+1) t
  have hL : (2*k:ℕ) ≤ dyadicIndex (m+1) t := by
    unfold dyadicIndex
    apply Nat.le_floor
    rw [Nat.cast_mul,pow_succ]
    push_cast
    nlinarith only [h.1]
  have hU : dyadicIndex (m+1) t < 2*k+2 := by
    unfold dyadicIndex
    apply (Nat.floor_lt (by positivity)).2
    rw [Nat.cast_add,Nat.cast_mul,pow_succ]
    push_cast
    nlinarith only [h.2]
  omega

theorem dyadicIndex_lt_compact {m M : ℕ} {t : ℝ≥0} (h : (t:ℝ)<(M:ℝ)) :
    dyadicIndex m t < M*2^m := by
  unfold dyadicIndex
  apply (Nat.floor_lt (by positivity)).2
  push_cast
  exact mul_lt_mul_of_pos_right h (by positivity)

theorem dyadic_round_dist_le (m : ℕ) (t : ℝ≥0) :
    dist (dyadicClock m (dyadicIndex m t)) t ≤ (1:ℝ)/(2:ℝ)^m := by
  change dist (dyadicClock m (dyadicIndex m t) : ℝ) (t:ℝ) ≤ _
  rw [Real.dist_eq,dyadicClock_coe]
  have hk := dyadicIndex_floor_bounds m t
  have h0 : (0:ℝ)<(2:ℝ)^m := by positivity
  have hL := (div_le_iff₀ h0).2 hk.1
  rw [abs_of_nonpos (sub_nonpos.mpr hL),neg_sub]
  rw [← mul_div_cancel_right₀ (t:ℝ) h0.ne',←sub_div]
  apply div_le_div_of_nonneg_right _ h0.le
  linarith only [hk.2]

theorem dyadicIndex_close_le {m : ℕ} {s t : ℝ≥0}
    (hst : (s:ℝ)≤(t:ℝ)) (h : (t:ℝ)-(s:ℝ)<(1:ℝ)/(2:ℝ)^m) :
    dyadicIndex m t=dyadicIndex m s ∨ dyadicIndex m t=dyadicIndex m s+1 := by
  have hm : (0:ℝ)<(2:ℝ)^m := by positivity
  have hl : dyadicIndex m s≤dyadicIndex m t :=
    Nat.floor_mono (mul_le_mul_of_nonneg_right hst hm.le)
  have hs := dyadicIndex_floor_bounds m s
  have ht := dyadicIndex_floor_bounds m t
  have He := (lt_div_iff₀ hm).1 h
  have hU : ((dyadicIndex m t):ℝ)<((dyadicIndex m s):ℝ)+2 := by
    rw [sub_mul] at He
    linarith only [He,hs.2,ht.1]
  have hU' : dyadicIndex m t < dyadicIndex m s+2 := by exact_mod_cast hU
  omega

#print axioms dyadicIndex_step
#print axioms dyadic_round_dist_le
#print axioms dyadicIndex_close_le
end CubeBrownian
