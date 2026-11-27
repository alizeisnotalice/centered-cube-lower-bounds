import SqrtOrdinalCyclicLabels
import SqrtPaperWalshCount

namespace CenteredCubeSqrt
open Classical
open scoped BigOperators
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

noncomputable def ordinalWalsh {b : ℕ} (a : NonzeroBinary b) (y : Fin (2^b)) : ℝ :=
  bitCharacter (∑ i, if a.1 i then (binaryLabelEquiv b).symm y i else 0)

/-- The actual defective cyclic fiber count in ordinal coordinates. -/
theorem defective_ordinal_walsh_count {b d : ℕ} (hd : 0 < d)
    (hb : 0 < b) (hdim : 2*b ≤ d)
    (g : (LabelField d)ˣ) (hg : orderOf g = 2^d-1) {t : Fin b → LabelField d}
    (ht : LinearIndependent (ZMod 2) t) (k : ZMod (2^d-1))
    (hk : (phaseState hd g hg k : LabelField d) ≠ 1)
    (hk' : (phaseState hd g hg k : LabelField d) ∈ labelRatioSet t)
    (hS : MultiplicativeSidon {x : LabelField d | x ∈ labelSpace t ∧ x ≠ 0})
    (a c : NonzeroBinary b)
    (hmatch : labelValue t a = (phaseState hd g hg k : LabelField d)*labelValue t c)
    (y z : Fin (2^b)) :
    (Nat.card {j : ZMod (2^d-1) //
      ordinalPhaseLabel hd g hg t j = y ∧ ordinalPhaseLabel hd g hg t (j+k) = z} : ℝ) =
      (2:ℝ)^d/((2:ℝ)^b)^2 * (1 + ordinalWalsh a y * ordinalWalsh c z) -
        (if (y,z) = (0,0) then 1 else 0) := by
  let u := (binaryLabelEquiv b).symm y
  let v := (binaryLabelEquiv b).symm z
  let target : LabelOutput b := Sum.elim u v
  have e0 : target = 0 ↔ y.val=0 ∧ z.val=0 := by
    constructor
    · intro h
      have hu : u=0 := by funext i; exact congrFun h (.inl i)
      have hv : v=0 := by funext i; exact congrFun h (.inr i)
      constructor
      · rw [← (binaryLabelEquiv b).apply_symm_apply y, show (binaryLabelEquiv b).symm y = 0 from hu]
        exact binaryLabelEquiv_zero b
      · rw [← (binaryLabelEquiv b).apply_symm_apply z, show (binaryLabelEquiv b).symm z = 0 from hv]
        exact binaryLabelEquiv_zero b
    · rintro ⟨hy,hz⟩
      have eu : (binaryLabelEquiv b) u = (binaryLabelEquiv b) 0 := by
        apply Fin.ext
        change ((binaryLabelEquiv b) ((binaryLabelEquiv b).symm y)).val = _
        rw [(binaryLabelEquiv b).apply_symm_apply y,binaryLabelEquiv_zero,hy]
      have ev : (binaryLabelEquiv b) v = (binaryLabelEquiv b) 0 := by
        apply Fin.ext
        change ((binaryLabelEquiv b) ((binaryLabelEquiv b).symm z)).val = _
        rw [(binaryLabelEquiv b).apply_symm_apply z,binaryLabelEquiv_zero,hz]
      have hu := (binaryLabelEquiv b).injective eu
      have hv := (binaryLabelEquiv b).injective ev
      funext i
      cases i with
      | inl i => exact congrFun hu i
      | inr i => exact congrFun hv i
  have eq : Nat.card {j : ZMod (2^d-1) //
      ordinalPhaseLabel hd g hg t j = y ∧ ordinalPhaseLabel hd g hg t (j+k) = z} =
      Nat.card {j : ZMod (2^d-1) //
      Sum.elim (phaseLabel hd g hg t j) (phaseLabel hd g hg t (j+k)) = target} := by
    apply Nat.card_congr (Equiv.subtypeEquiv (Equiv.refl _) ?_)
    intro j
    constructor
    · rintro ⟨h1,h2⟩
      have h1' : phaseLabel hd g hg t j = u := by
        apply (binaryLabelEquiv b).injective
        rwa [show (binaryLabelEquiv b) u = y from (binaryLabelEquiv b).apply_symm_apply y]
      have h2' : phaseLabel hd g hg t (j+k) = v := by
        apply (binaryLabelEquiv b).injective
        rwa [show (binaryLabelEquiv b) v = z from (binaryLabelEquiv b).apply_symm_apply z]
      change Sum.elim (phaseLabel hd g hg t j) (phaseLabel hd g hg t (j+k)) = target
      rw [h1',h2']
    · intro h
      have h1' : phaseLabel hd g hg t j = u := by funext i; exact congrFun h (.inl i)
      have h2' : phaseLabel hd g hg t (j+k) = v := by funext i; exact congrFun h (.inr i)
      unfold ordinalPhaseLabel
      rw [h1', h2']
      exact ⟨(binaryLabelEquiv b).apply_symm_apply y,(binaryLabelEquiv b).apply_symm_apply z⟩
  rw [eq, manuscript_defective_walsh_count hd hb hdim g hg ht k hk hk' hS a c hmatch]
  have eq0 : target = 0 ↔ (y,z) = (0,0) := by
    rw [e0, Prod.mk_inj]
    exact and_congr (⟨fun h => Fin.ext (by simpa using h), fun h => by simpa using congrArg Fin.val h⟩) (⟨fun h => Fin.ext (by simpa using h), fun h => by simpa using congrArg Fin.val h⟩)
  simp only [eq0]
  rfl

#print axioms defective_ordinal_walsh_count

end CenteredCubeSqrt
