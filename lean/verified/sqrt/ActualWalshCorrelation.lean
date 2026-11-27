import DefectWeighted
import WalshPrimitive
import SqrtCyclicSafety

namespace CenteredCubeSqrt
open MeasureTheory Set Classical
open scoped BigOperators Interval
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem actual_walsh_match_of_defect {b d : ℕ} (hd : 0<d)
    (g : (LabelField d)ˣ) (hg : orderOf g=2^d-1) {t : Fin b → LabelField d}
    (k : ZMod (2^d-1)) (hk : k ∈ cyclicDefects hd g hg t) :
    ∃ a c : NonzeroBinary b, a ≠ c ∧
      labelValue t a = (phaseState hd g hg k : LabelField d)*labelValue t c := by
  obtain ⟨u,hu,v,hv,hu0,hv0,huv,he⟩ := hk
  obtain ⟨a,ha⟩ := labelSpace_nonzero_is_labelValue t hu hu0
  obtain ⟨c,hc⟩ := labelSpace_nonzero_is_labelValue t hv hv0
  refine ⟨a,c,fun e => huv (ha.symm.trans (e ▸ hc)),?_⟩
  change u / v = (phaseState hd g hg k : LabelField d) at he
  rw [ha,hc,←he]
  field_simp

noncomputable def rawWalshLeft {b : ℕ} (θ : ℝ) (a c : NonzeroBinary b) : ℝ :=
  ∫ r in (0:ℝ)..1-θ, walshCellPrimitive a r * walshCellPrimitive c (r+θ)

noncomputable def rawWalshRight {b : ℕ} (θ : ℝ) (a c : NonzeroBinary b) : ℝ :=
  ∫ r in 1-θ..(1:ℝ), walshCellPrimitive a r * walshCellPrimitive c (r+θ-1)

theorem raw_left_walsh_factor {b : ℕ} {θ : ℝ} (hθ : θ ∈ Icc (0:ℝ) 1)
    (a c : NonzeroBinary b) :
    (1/((2:ℝ)^b)^2)*(∑ p : Fin (2^b) × Fin (2^b),
      ordinalWalsh a p.1 * ordinalWalsh c p.2 * rawCellMomentLeft θ p) = rawWalshLeft θ a c :=
  walshCell_moment a c (by linarith [hθ.2]) (by norm_num) (by linarith [hθ.1]) (by linarith [hθ.1]) (by linarith)

theorem raw_right_walsh_factor {b : ℕ} {θ : ℝ} (hθ : θ ∈ Icc (0:ℝ) 1)
    (a c : NonzeroBinary b) :
    (1/((2:ℝ)^b)^2)*(∑ p : Fin (2^b) × Fin (2^b),
      ordinalWalsh a p.1 * ordinalWalsh c p.2 * rawCellMomentRight θ p) = rawWalshRight θ a c := by
  have h := walshCell_moment (l:=1-θ) (r:=1) (s:=θ-1) a c
    (by linarith [hθ.1]) (by linarith [hθ.2]) (by norm_num) (by linarith) (by linarith [hθ.2])
  simpa only [rawCellMomentRight,rawWalshRight,add_sub_assoc] using h

theorem actual_raw_correlation_from_split_pair_laws {b d : ℕ} [NeZero (2^d-1)]
    (hd : 0<d) (g : (LabelField d)ˣ) (hg : orderOf g=2^d-1) {t : Fin b → LabelField d}
    (ht : LinearIndependent (ZMod 2) t) (hdim : 2*b≤d) (k : ℤ) {θ : ℝ} (hθ : θ∈Icc (0:ℝ) 1)
    (D₁ D₂ : ℝ)
    (hL : let f := ordinalPhaseLabel hd g hg t
      let wL := rawCellMomentLeft (B:=2^b) θ
      (∑ j : ZMod (2^d-1), wL (f j, f (j+(k:ZMod (2^d-1))))) =
        (2:ℝ)^d/((2:ℝ)^b)^2*(∑ p, wL p)-wL (0,0)+(2:ℝ)^d*D₁)
    (hR : let f := ordinalPhaseLabel hd g hg t
      let wR := rawCellMomentRight (B:=2^b) θ
      (∑ j : ZMod (2^d-1), wR (f j, f (j+((k:ZMod (2^d-1))+1)))) =
        (2:ℝ)^d/((2:ℝ)^b)^2*(∑ p, wR p)-wR (0,0)+(2:ℝ)^d*D₂) :
    let f := ordinalPhaseLabel hd g hg t
    let B := 2^b
    let K := ((2^d-1:ℕ):ℝ)
    let q := (2:ℝ)^d
    rawCorrelation f ((k:ℝ)+θ) =
      (q/K)*(unitRotatedInner (midpointError B) θ + D₁ + D₂) -
      (1/K)*unitRotatedInner (cellPrimitive (labelCellMidpoint (0:Fin (2^b)))) θ := by
  let f := ordinalPhaseLabel hd g hg t
  let B := (2^b:ℕ)
  let K := ((2^d-1:ℕ):ℝ)
  let q := (2:ℝ)^d
  let E := midpointError B
  let P := cellPrimitive (labelCellMidpoint (0:Fin (2^b)))
  let wL := rawCellMomentLeft (B:=B) θ
  let wR := rawCellMomentRight (B:=B) θ
  change rawCorrelation f ((k:ℝ)+θ) = (q/K)*(unitRotatedInner E θ + D₁ + D₂)-(1/K)*unitRotatedInner P θ
  rw [rawCorrelation_cell_decomp f k hθ,Finset.sum_add_distrib,
    sum_zmod_natRange (fun j => wL (f j,f (j+(k:ZMod (2^d-1))))),
    sum_zmod_natRange (fun j => wR (f j,f (j+(k:ZMod (2^d-1))+1)))]
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
  change (1/K)*((q/(B:ℝ)^2*(∑ p : Fin B × Fin B,wL p)-wL (0,0)+q*D₁)+
    (q/(B:ℝ)^2*(∑ p : Fin B × Fin B,wR p)-wR (0,0)+q*D₂)) = _
  have e1 : unitRotatedInner E θ=IL+IR := rfl
  have e2 : unitRotatedInner P θ=wL (0,0)+wR (0,0) := rfl
  rw [e1,e2]
  rw [show q/(B:ℝ)^2*(∑ p : Fin B × Fin B,wL p)=q*IL by rw [←eL]; ring,
    show q/(B:ℝ)^2*(∑ p : Fin B × Fin B,wR p)=q*IR by rw [←eR]; ring]
  ring

#print axioms actual_raw_correlation_from_split_pair_laws
#print axioms actual_walsh_match_of_defect
#print axioms raw_left_walsh_factor
#print axioms raw_right_walsh_factor
end CenteredCubeSqrt
