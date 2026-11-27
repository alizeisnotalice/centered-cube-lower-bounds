import SqrtRawDiagonalSafe
namespace CenteredCubeSqrt
open MeasureTheory Set
open scoped Interval BigOperators
set_option maxHeartbeats 1000000
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

noncomputable def rawNearMain (B : ℕ) (θ : ℝ) :=
  (1/(B:ℝ))*(∑ y : Fin B,rawCellMomentLeft θ (y,y)) +
  (1/(B:ℝ)^2)*(∑ p : Fin B × Fin B,rawCellMomentRight θ p)

theorem raw_regular_marginal_sum {b d : ℕ} [NeZero (2^d-1)] (hd : 0<d)
    (g : (LabelField d)ˣ) (hg : orderOf g=2^d-1) {t : Fin b → LabelField d}
    (ht : LinearIndependent (ZMod 2) t) (hdim : 2*b≤d)
    (k : ZMod (2^d-1)) (hk : (phaseState hd g hg k : LabelField d) ≠ 1)
    (hk' : (phaseState hd g hg k : LabelField d) ∉ labelRatioSet t) (w : Fin (2^b)→ℝ) :
    let f := ordinalPhaseLabel hd g hg t
    let B := (2:ℝ)^b
    let q := (2:ℝ)^d
    (∑ j : ZMod (2^d-1), w (f j)) = (q/B)*(∑ y : Fin (2^b), w y)-w 0 := by
  let f := ordinalPhaseLabel hd g hg t
  let B := (2:ℝ)^b
  let q := (2:ℝ)^d
  have hB : 0<B := by dsimp [B]; positivity
  have h := raw_regular_pair_sum hd g hg ht k hk hk' hdim (fun p => w p.1)
  change (∑ j : ZMod (2^d-1),w (f j)) =
    q/B^2*(∑ p : Fin (2^b) × Fin (2^b), w p.1)-w 0 at h
  rw [Fintype.sum_prod_type] at h
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat] at h
  rw [←Finset.mul_sum] at h
  change (∑ j : ZMod (2^d-1),w (f j)) = (q/B)*(∑ y : Fin (2^b), w y)-w 0
  rw [h]
  change q/B^2*(B*(∑ y : Fin (2^b),w y))-w 0=(q/B)*(∑ y : Fin (2^b),w y)-w 0
  field_simp [hB.ne']

theorem actual_raw_near_correlation_exact {b d : ℕ} [NeZero (2^d-1)]
    (hd : 0<d) (g : (LabelField d)ˣ) (hg : orderOf g=2^d-1) {t : Fin b → LabelField d}
    (ht : LinearIndependent (ZMod 2) t) (hdim : 2*b≤d) {θ : ℝ} (hθ : θ∈Icc (0:ℝ) 1)
    (h1 : (phaseState hd g hg (1:ZMod (2^d-1)) : LabelField d) ≠ 1)
    (h1' : (phaseState hd g hg (1:ZMod (2^d-1)) : LabelField d) ∉ labelRatioSet t) :
    let f := ordinalPhaseLabel hd g hg t
    let K := ((2^d-1:ℕ):ℝ)
    let q := (2:ℝ)^d
    rawCorrelation f θ = (q/K)*rawNearMain (2^b) θ -
      (1/K)*unitRotatedInner (cellPrimitive (labelCellMidpoint (0:Fin (2^b)))) θ := by
  let f := ordinalPhaseLabel hd g hg t
  let K := ((2^d-1:ℕ):ℝ)
  let q := (2:ℝ)^d
  let B := (2^b:ℕ)
  let L := rawCellMomentLeft (B:=B) θ
  let R := rawCellMomentRight (B:=B) θ
  have e := rawCorrelation_cell_decomp f (0:ℤ) hθ
  simp only [Int.cast_zero,zero_add,add_zero,Finset.sum_add_distrib] at e
  rw [sum_zmod_natRange (fun j => L (f j,f j)),sum_zmod_natRange (fun j => R (f j,f (j+1)))] at e
  have hL := raw_regular_marginal_sum hd g hg ht hdim 1 h1 h1' (fun y => L (y,y))
  have hR := raw_regular_pair_sum hd g hg ht 1 h1 h1' hdim R
  change rawCorrelation f θ=(q/K)*rawNearMain B θ-
    (1/K)*unitRotatedInner (cellPrimitive (labelCellMidpoint (0:Fin (2^b)))) θ
  rw [e,hL,hR]
  have hbr : (B:ℝ)=(2:ℝ)^b := by dsimp [B]; norm_cast
  rw [←hbr]
  unfold rawNearMain unitRotatedInner
  change (1/K)*((q/(B:ℝ)*(∑ y : Fin B,L (y,y))-L (0,0))+
    (q/(B:ℝ)^2*(∑ p : Fin B × Fin B,R p)-R (0,0))) =
    (q/K)*((1/(B:ℝ))*(∑ y : Fin B,L (y,y)) + (1/(B:ℝ)^2)*(∑ p : Fin B × Fin B,R p)) -
      (1/K)*(L (0,0)+R (0,0))
  ring

#print axioms actual_raw_near_correlation_exact
end CenteredCubeSqrt
