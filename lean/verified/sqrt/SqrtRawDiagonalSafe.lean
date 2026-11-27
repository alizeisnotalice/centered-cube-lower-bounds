import SqrtRawRegularCorrelation
import SqrtRawWindowCovariance
import SqrtSafeCoarseLifts

namespace CenteredCubeSqrt
open MeasureTheory Set
open scoped Interval BigOperators
set_option maxHeartbeats 1800000
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem actual_raw_regular_correlation_bound {b d : ℕ} [NeZero (2^d-1)]
    (hd : 0<d) (g : (LabelField d)ˣ) (hg : orderOf g=2^d-1) {t : Fin b → LabelField d}
    (ht : LinearIndependent (ZMod 2) t) (hdim : 2*b≤d) (k : ℤ) {θ : ℝ} (hθ : θ∈Icc (0:ℝ) 1)
    (hk : (phaseState hd g hg (k:ZMod (2^d-1)) : LabelField d) ≠ 1)
    (hk' : (phaseState hd g hg (k:ZMod (2^d-1)) : LabelField d) ∉ labelRatioSet t)
    (hks : (phaseState hd g hg ((k:ZMod (2^d-1))+1) : LabelField d) ≠ 1)
    (hks' : (phaseState hd g hg ((k:ZMod (2^d-1))+1) : LabelField d) ∉ labelRatioSet t) :
    |rawCorrelation (ordinalPhaseLabel hd g hg t) ((k:ℝ)+θ)| ≤
      1/(12*((2:ℝ)^b)^2)+1/(2*(((2^d-1:ℕ):ℝ))) := by
  let B := (2^b:ℕ)
  let K := ((2^d-1:ℕ):ℝ)
  let E := midpointError B
  let P := cellPrimitive (labelCellMidpoint (0:Fin (2^b)))
  let R := unitRotatedInner E θ
  let S := unitRotatedInner P θ
  let ε := 1/(12*(B:ℝ)^2)
  have hk0 : 0<K := by
    dsimp [K]
    exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne (2^d-1)))
  have hB : 0<B := by unfold B; positivity
  have hB1 : 1≤(B:ℝ) := by exact_mod_cast Nat.succ_le_of_lt hB
  have hε : ε≤1/6 := by
    unfold ε
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [pow_le_pow_left₀ (show (0:ℝ)≤1 by norm_num) hB1 2]
  have h1 := unitRotatedInner_abs_le_energy hθ (midpointError_measurable hB)
    (fun r hr => midpointError_abs_le_one hB hr)
  rw [midpointError_period_energy hB] at h1
  have h1' : |R|≤ε := h1
  have h2 := unitRotatedInner_abs_le_energy (f:=P) (A:=1) hθ (cellPrimitive_measurable _)
    (fun _ hr => cellPrimitive_abs_le_one (u:=labelCellMidpoint (0:Fin (2^b))) hr)
  have h3 : |S|≤1/3 := h2.trans (label_zero_energy_le_third (B:=2^b) hB)
  have hq : (2:ℝ)^d=K+1 := by
    have h : 0<(2^d:ℕ) := by positivity
    dsimp [K]
    exact_mod_cast (Nat.sub_add_cancel (show 1≤(2^d:ℕ) by omega)).symm
  rw [actual_raw_regular_correlation_exact hd g hg ht hdim k hθ hk hk' hks hks']
  change |((2:ℝ)^d/K)*R-(1/K)*S|≤1/(12*((2:ℝ)^b)^2)+1/(2*K)
  rw [hq,show ((K+1)/K)*R-(1/K)*S=R+(1/K)*(R-S) by field_simp; ring]
  have hh := abs_add_le R ((1/K)*(R-S))
  rw [abs_mul,abs_of_nonneg (by positivity : 0≤1/K)] at hh
  refine hh.trans ?_
  have h' : |R-S|≤1/2 :=
    (show |R-S|≤|R|+|S| from by simpa only [sub_eq_add_neg,abs_neg] using abs_add_le R (-S)).trans (by linarith)
  have he : ((B:ℕ):ℝ)=(2:ℝ)^b := by dsimp [B]; norm_cast
  rw [←he]
  exact (add_le_add h1 (mul_le_mul_of_nonneg_left h' (by positivity))).trans_eq (by ring)

#print axioms actual_raw_regular_correlation_bound
end CenteredCubeSqrt
