import SqrtRawRotation
import SqrtRawZeroCorrelation

namespace CenteredCubeSqrt
open MeasureTheory Set
open scoped Interval BigOperators
set_option maxHeartbeats 1800000
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem cellPrimitive_measurable (u : ℝ) : Measurable (cellPrimitive u) := by
  unfold cellPrimitive
  exact (Measurable.ite (measurableSet_Ici : MeasurableSet (Ici u)) measurable_const measurable_const).sub measurable_id

theorem midpointError_measurable {B : ℕ} (hB : 0<B) : Measurable (midpointError B) := by
  have eq : midpointError B = fun r => (∑ y : Fin B,cellPrimitive (labelCellMidpoint y) r)/(B:ℝ) :=
    funext (fun r => (cellPrimitive_label_mean hB r).symm)
  rw [eq]
  exact (Finset.measurable_sum _ (fun y _ => cellPrimitive_measurable (labelCellMidpoint y))).div_const _

theorem midpointError_abs_le_one {B : ℕ} (hB : 0<B) {r : ℝ} (hr : r∈Icc (0:ℝ) 1) :
    |midpointError B r|≤1 := by
  rw [←cellPrimitive_label_mean hB]
  have hB' : 0<(B:ℝ) := by exact_mod_cast hB
  rw [abs_div,abs_of_pos hB',div_le_one hB']
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have H := Finset.sum_le_sum (fun y (_ : y∈(Finset.univ : Finset (Fin B))) =>
    cellPrimitive_abs_le_one (u:=labelCellMidpoint y) hr)
  exact H.trans_eq (by simp)

theorem actual_raw_regular_correlation_exact {b d : ℕ} [NeZero (2^d-1)]
    (hd : 0<d) (g : (LabelField d)ˣ) (hg : orderOf g=2^d-1) {t : Fin b → LabelField d}
    (ht : LinearIndependent (ZMod 2) t) (hdim : 2*b≤d) (k : ℤ) {θ : ℝ} (hθ : θ∈Icc (0:ℝ) 1)
    (hk : (phaseState hd g hg (k:ZMod (2^d-1)) : LabelField d) ≠ 1)
    (hk' : (phaseState hd g hg (k:ZMod (2^d-1)) : LabelField d) ∉ labelRatioSet t)
    (hks : (phaseState hd g hg ((k:ZMod (2^d-1))+1) : LabelField d) ≠ 1)
    (hks' : (phaseState hd g hg ((k:ZMod (2^d-1))+1) : LabelField d) ∉ labelRatioSet t) :
    let f := ordinalPhaseLabel hd g hg t
    let B := 2^b
    let K := ((2^d-1:ℕ):ℝ)
    let q := (2:ℝ)^d
    rawCorrelation f ((k:ℝ)+θ) =
      (q/K)*unitRotatedInner (midpointError B) θ -
      (1/K)*unitRotatedInner (cellPrimitive (labelCellMidpoint (0:Fin (2^b)))) θ := by
  let f := ordinalPhaseLabel hd g hg t
  let B := (2^b:ℕ)
  let K := ((2^d-1:ℕ):ℝ)
  let q := (2:ℝ)^d
  let E := midpointError B
  let P := cellPrimitive (labelCellMidpoint (0:Fin (2^b)))
  let wL := rawCellMomentLeft (B:=B) θ
  let wR := rawCellMomentRight (B:=B) θ
  change rawCorrelation f ((k:ℝ)+θ) = (q/K)*unitRotatedInner E θ-(1/K)*unitRotatedInner P θ
  rw [rawCorrelation_cell_decomp f k hθ,Finset.sum_add_distrib,
    sum_zmod_natRange (fun j => wL (f j,f (j+(k:ZMod (2^d-1))))),
    sum_zmod_natRange (fun j => wR (f j,f (j+(k:ZMod (2^d-1))+1)))]
  have hL := raw_regular_pair_sum hd g hg ht (k:ZMod (2^d-1)) hk hk' hdim wL
  have hR := raw_regular_pair_sum hd g hg ht ((k:ZMod (2^d-1))+1) hks hks' hdim wR
  change (1/K)*((∑ j : ZMod (2^d-1),wL (f j,f (j+(k:ZMod (2^d-1)))))+
    (∑ j : ZMod (2^d-1),wR (f j,f ((j+(k:ZMod (2^d-1)))+1)))) = _
  simp_rw [add_assoc _ (k:ZMod (2^d-1)) 1]
  rw [hL,hR]
  let IL := ∫ r in (0:ℝ)..1-θ, E r*E (r+θ)
  let IR := ∫ r in (1-θ:ℝ)..1,E r*E (r+θ-1)
  have hB : 0<B := by dsimp [B]; positivity
  have heL := rawCellUniformPair_moment (B:=B) hB (a:=0) (b:=1-θ) (s:=θ)
    (by linarith [hθ.2]) (by norm_num) (by linarith [hθ.1]) (by linarith [hθ.1]) (by linarith)
  have heR := rawCellUniformPair_moment (B:=B) hB (a:=1-θ) (b:=1) (s:=θ-1)
    (by linarith [hθ.1]) (by linarith [hθ.2]) (by norm_num) (by linarith) (by linarith [hθ.2])
  have eL : (1/(B:ℝ)^2)*(∑ p : Fin B × Fin B,wL p)=IL := heL
  have eR : (1/(B:ℝ)^2)*(∑ p : Fin B × Fin B,wR p)=IR := by
    simp_rw [←add_sub_assoc] at heR
    exact heR
  have hbr : (B:ℝ)=(2:ℝ)^b := by dsimp [B]; norm_cast
  rw [←hbr]
  change (1/K)*((q/(B:ℝ)^2*(∑ p : Fin B × Fin B,wL p)-wL (0,0))+
    (q/(B:ℝ)^2*(∑ p : Fin B × Fin B,wR p)-wR (0,0))) = _
  have e1 : unitRotatedInner E θ=IL+IR := rfl
  have e2 : unitRotatedInner P θ=wL (0,0)+wR (0,0) := rfl
  rw [e1,e2]
  rw [show q/(B:ℝ)^2*(∑ p : Fin B × Fin B,wL p)=q*IL by rw [←eL]; ring,
    show q/(B:ℝ)^2*(∑ p : Fin B × Fin B,wR p)=q*IR by rw [←eR]; ring]
  ring

#print axioms actual_raw_regular_correlation_exact
end CenteredCubeSqrt
