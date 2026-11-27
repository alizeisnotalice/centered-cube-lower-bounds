import SqrtRawDiagonalArithmetic
import SqrtRawRegularPair
import SqrtRawCorrelation

namespace CenteredCubeSqrt
open MeasureTheory Set
open scoped Interval BigOperators
set_option maxHeartbeats 1600000
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem sum_zmod_natRange {K : ℕ} [NeZero K] (w : ZMod K→ℝ) :
    (∑ j ∈ Finset.range K, w (j:ZMod K))=∑ j : ZMod K,w j := by
  rw [←Fin.sum_univ_eq_sum_range]
  refine Fintype.sum_equiv (ZMod.finEquiv K).toEquiv _ _ (fun j => ?_)
  congr 1
  apply ZMod.val_injective K
  rw [ZMod.val_natCast_of_lt j.isLt]
  cases K with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ K => rfl

theorem rawCorrelation_zero_eq_cell_energy {B K : ℕ} [NeZero K] (f : ZMod K → Fin B) :
    rawCorrelation f 0=(1/(K:ℝ))*(∑ j : ZMod K, ∫ r in (0:ℝ)..1,
      (cellPrimitive (labelCellMidpoint (f j)) r)^2) := by
  have h := rawCorrelation_cell_decomp f (0:ℤ) (θ:=0) (by norm_num)
  simp only [Int.cast_zero,add_zero,rawCellMomentLeft,rawCellMomentRight,sub_zero,
    intervalIntegral.integral_same,pow_two] at h ⊢
  rw [h]
  exact congrArg (fun x : ℝ => (1/(K:ℝ))*x)
    (sum_zmod_natRange (K:=K) (fun j => ∫ r in (0:ℝ)..1,
      cellPrimitive (labelCellMidpoint (f j)) r*cellPrimitive (labelCellMidpoint (f j)) r))

theorem actual_raw_zero_correlation_exact {b d : ℕ} [NeZero (2^d-1)] (hd : 0<d)
    (g : (LabelField d)ˣ) (hg : orderOf g=2^d-1) {t : Fin b → LabelField d}
    (ht : LinearIndependent (ZMod 2) t) (k : ZMod (2^d-1))
    (hk : (phaseState hd g hg k : LabelField d) ≠ 1)
    (hk' : (phaseState hd g hg k : LabelField d) ∉ labelRatioSet t)
    (hdim : 2*b≤d) :
    let f := ordinalPhaseLabel hd g hg t
    let B := (2:ℝ)^b
    let q := (2:ℝ)^d
    let K := ((2^d-1:ℕ):ℝ)
    rawCorrelation f 0 =
      (q/K)*(1/6-1/(12*B^2)) -
      (1/K)*(∫ r in (0:ℝ)..1,(cellPrimitive (labelCellMidpoint (0:Fin (2^b))) r)^2) := by
  let f := ordinalPhaseLabel hd g hg t
  let B := (2:ℝ)^b
  let q := (2:ℝ)^d
  let K := ((2^d-1:ℕ):ℝ)
  let w (y : Fin (2^b)) := ∫ r in (0:ℝ)..1,(cellPrimitive (labelCellMidpoint y) r)^2
  have hB : 0<B := by dsimp [B]; positivity
  have h := raw_regular_pair_sum hd g hg ht k hk hk' hdim (fun p => w p.1)
  change (∑ j : ZMod (2^d-1),w (f j)) = q/B^2*(∑ p : Fin (2^b) × Fin (2^b), w p.1)-w 0 at h
  rw [Fintype.sum_prod_type] at h
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat] at h
  rw [←Finset.mul_sum] at h
  have he := one_cell_average_raw_energy (show 0<(2^b:ℕ) by positivity)
  change (1/((2^b:ℕ):ℝ))*(∑ y : Fin (2^b), w y) = 1/6-1/(12*(((2^b:ℕ):ℝ))^2) at he
  push_cast at he
  change (1/B)*(∑ y : Fin (2^b),w y)=1/6-1/(12*B^2) at he
  change rawCorrelation f 0 = (q/K)*(1/6-1/(12*B^2))-(1/K)*w 0
  rw [rawCorrelation_zero_eq_cell_energy]
  change (1/K)*(∑ j : ZMod (2^d-1),w (f j)) = _
  rw [h,←he]
  field_simp [hB.ne']
  ring

#print axioms actual_raw_zero_correlation_exact
end CenteredCubeSqrt
