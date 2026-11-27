import SqrtRatioExclusions
import SqrtActualCyclicFibers

namespace CenteredCubeSqrt

open MvPolynomial 
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- The exact defect residues in the manuscript's (Z/KZ), not the
unlogged field ratios. -/
noncomputable def cyclicDefects {b d : ℕ} (hd : 0 < d) (g : (LabelField d)ˣ)
    (hg : orderOf g = 2^d-1) (t : Fin b → LabelField d) : Set (ZMod (2^d-1)) :=
  (fun j => (phaseState hd g hg j : LabelField d)) ⁻¹' labelRatioSet t

theorem cyclicDefects_card {b d : ℕ} (hd : 0 < d) (g : (LabelField d)ˣ)
    (hg : orderOf g = 2^d-1) {t : Fin b → LabelField d}
    (h0 : ∀ a, labelValue t a ≠ 0)
    (hp : Function.Injective (fun z : Sym2 (NonzeroBinary b) => eval t (symLabelProduct z))) :
    (cyclicDefects hd g hg t).ncard = (2^b-1)*(2^b-2) := by
  have hi : Function.Injective (fun j => (phaseState hd g hg j : LabelField d)) := by
    intro j k e
    have hh := (cyclicStateEquiv hd g hg).injective (Units.ext e)
    exact congrArg Multiplicative.toAdd hh
  rw [cyclicDefects, Set.ncard_preimage_of_injective_subset_range hi, labelRatioSet_ncard h0 hp]
  rintro x ⟨a,ha,c,hc,a0,c0,_,he⟩
  have hx : x ≠ 0 := by rw [← he]; exact div_ne_zero a0 c0
  let u := Units.mk0 x hx
  let j := ((cyclicStateEquiv hd g hg).symm u).toAdd
  refine ⟨j,?_⟩
  change ((cyclicStateEquiv hd g hg) ((cyclicStateEquiv hd g hg).symm u) : LabelField d)=x
  rw [MulEquiv.apply_symm_apply]
  rfl

theorem cyclicDefects_zero_notMem {b d : ℕ} (hd : 0 < d) (g : (LabelField d)ˣ)
    (hg : orderOf g = 2^d-1) (t : Fin b → LabelField d) :
    0 ∉ cyclicDefects hd g hg t := by
  change (phaseState hd g hg 0 : LabelField d) ∉ labelRatioSet t
  rw [show phaseState hd g hg 0=1 from map_one (cyclicStateEquiv hd g hg)]
  exact labelRatioSet_one_notMem t

theorem cyclicDefects_step_excluded {b d : ℕ} (hd : 0 < d) (g : (LabelField d)ˣ)
    (hg : orderOf g = 2^d-1) {t : Fin b → LabelField d}
    (h0 : ∀ a, labelValue t a ≠ 0)
    (hp : Function.Injective (fun z : Sym2 (NonzeroBinary b) => eval t (symLabelProduct z)))
    (he : ∀ p q : UnequalLabels b,
      labelValue t p.1.1 * labelValue t q.1.2 ≠
      (g:LabelField d) * (labelValue t p.1.2 * labelValue t q.1.1))
    {j : ZMod (2^d-1)} (hj : j ∈ cyclicDefects hd g hg t) :
    j+1 ∉ cyclicDefects hd g hg t := by
  change (phaseState hd g hg j : LabelField d) ∈ labelRatioSet t at hj
  change (phaseState hd g hg (j+1) : LabelField d) ∉ labelRatioSet t
  have e : phaseState hd g hg (j+1) = phaseState hd g hg j * g := by
    unfold phaseState
    rw [cyclicStateEquiv_shift]
    rw [cyclicStateEquiv, zmodMulEquivOfGenerator_apply_ofAdd_one]
  rw [e, Units.val_mul, mul_comm]
  exact labelRatioSet_no_neighbor h0 hp he hj

#print axioms cyclicDefects_card
#print axioms cyclicDefects_zero_notMem
#print axioms cyclicDefects_step_excluded

end CenteredCubeSqrt
