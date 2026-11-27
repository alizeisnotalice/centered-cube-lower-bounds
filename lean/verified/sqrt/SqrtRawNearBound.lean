import SqrtRawNearEnergy
import SqrtRawNearQuantitative

namespace CenteredCubeSqrt
open MeasureTheory Set
open scoped Interval BigOperators
set_option maxHeartbeats 1000000
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem actual_raw_near_correlation_bound {b d : ℕ} [NeZero (2^d-1)]
    (hd : 0<d) (g : (LabelField d)ˣ) (hg : orderOf g=2^d-1) {t : Fin b → LabelField d}
    (ht : LinearIndependent (ZMod 2) t) (hdim : 2*b≤d) {θ : ℝ} (hθ : θ∈Icc (0:ℝ) 1)
    (h1 : (phaseState hd g hg (1:ZMod (2^d-1)) : LabelField d) ≠ 1)
    (h1' : (phaseState hd g hg (1:ZMod (2^d-1)) : LabelField d) ∉ labelRatioSet t) :
    let f := ordinalPhaseLabel hd g hg t
    let K := ((2^d-1:ℕ):ℝ)
    |rawCorrelation f θ-(1-θ)^3/6|≤1/(4*((2:ℝ)^b)^2)+1/(2*K) := by
  dsimp only
  let K := ((2^d-1:ℕ):ℝ)
  let B := (2^b:ℕ)
  let L := rawNearMain B θ
  let Z := unitRotatedInner (cellPrimitive (labelCellMidpoint (0:Fin B))) θ
  let P := (1-θ)^3/6
  have hK : 0<K := by
    dsimp [K]
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne (2^d-1))
  have hB : 0<B := by dsimp [B]; positivity
  have hq : (2:ℝ)^d=K+1 := by
    have hp : 0<(2^d:ℕ) := by positivity
    dsimp [K]
    exact_mod_cast (Nat.sub_add_cancel (show 1≤(2^d:ℕ) by omega)).symm
  have hL : |L|≤1/6 := (rawNearMain_abs_energy_bound hB hθ).trans (sub_le_self _ (by positivity))
  have hP : |L-P|≤1/(4*(B:ℝ)^2) := rawNearMain_quantization_bound hB hθ
  have hZ : |Z|≤1/3 := by
    have h := unitRotatedInner_abs_le_energy (f:=cellPrimitive (labelCellMidpoint (0:Fin B))) (A:=1)
      hθ (cellPrimitive_measurable _) (fun _ hr => cellPrimitive_abs_le_one (u:=labelCellMidpoint (0:Fin B)) hr)
    exact h.trans (label_zero_energy_le_third (B:=B) hB)
  rw [actual_raw_near_correlation_exact hd g hg ht hdim hθ h1 h1']
  change |((2:ℝ)^d/K)*L-(1/K)*Z-P|≤1/(4*((2:ℝ)^b)^2)+1/(2*K)
  rw [hq,show ((K+1)/K)*L-(1/K)*Z-P=(L-P)+(1/K)*(L-Z) by field_simp; ring]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul,abs_of_nonneg (by positivity : 0≤1/K)]
  have hT : |L-Z|≤1/2 := by
    have h := abs_add_le L (-Z)
    rw [←sub_eq_add_neg,abs_neg] at h
    exact h.trans (by linarith)
  have hbr : (B:ℝ)=(2:ℝ)^b := by dsimp [B]; norm_cast
  rw [←hbr]
  exact (add_le_add hP (mul_le_mul_of_nonneg_left hT (by positivity))).trans_eq (by ring)

#print axioms actual_raw_near_correlation_bound
end CenteredCubeSqrt
