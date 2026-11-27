import SqrtPhysicalCarry
import SqrtPhysicalOrdinalFibers
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring

namespace CenteredCubeSqrt

open Classical

/-- Literal ordered atom pairs satisfying the fine circular congruence. -/
noncomputable def circularAtomHits {B K : ℕ} [NeZero K] (f : ZMod K → Fin B) (ell : ℤ) :
    Finset (ZMod K × ZMod K) :=
  Finset.univ.filter fun p =>
    labelCoord (B:ℤ) (p.2.val:ℤ) ((f p.2).val:ℤ) -
    labelCoord (B:ℤ) (p.1.val:ℤ) ((f p.1).val:ℤ) ≡ ell [ZMOD (B:ℤ)*K]

def lagPairEmbedding {K : ℕ} (k : ZMod K) : ZMod K ↪ ZMod K × ZMod K where
  toFun j := (j,j+k)
  inj' _ _ e := congrArg Prod.fst e

theorem modEq_phase_iff {K : ℕ} [NeZero K] {j l : ZMod K} {k : ℤ} :
    ((l.val:ℤ)-(j.val:ℤ) ≡ k [ZMOD (K:ℤ)]) ↔ l = j+(k : ZMod K) := by
  rw [Int.modEq_iff_dvd, ← ZMod.intCast_eq_intCast_iff_dvd_sub, Int.cast_sub,
    Int.cast_natCast, Int.cast_natCast, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
  constructor
  · intro h
    calc
      l = l-j+j := (sub_add_cancel _ _).symm
      _ = j+(k:ZMod K) := by rw [h,add_comm]
  · intro h
    rw [h,add_comm j,add_sub_cancel_right]

/-- The two regular carry classes give a disjoint partition of the actual
ordered pair set, not merely counts in an auxiliary digit space. -/
theorem circular_atom_count_as_lags {B K b : ℕ} [NeZero K] (hb : b < B)
    (f : ZMod K → Fin B) (k : ℤ) :
    (circularAtomHits f (k*B+b)).card =
      (ordinalLagHits f (k : ZMod K) b).card +
      (ordinalLagHits f ((k+1 : ℤ) : ZMod K) ((b:ℤ)-B)).card := by
  let A := (ordinalLagHits f (k : ZMod K) b).map (lagPairEmbedding (k : ZMod K))
  let D := (ordinalLagHits f ((k+1:ℤ) : ZMod K) ((b:ℤ)-B)).map
    (lagPairEmbedding ((k+1:ℤ) : ZMod K))
  have aMem (p : ZMod K × ZMod K) : p ∈ A ↔
      p.2 = p.1+(k : ZMod K) ∧ (↑(f p.2).val : ℤ) - ↑(f p.1).val = b := by
    unfold A
    constructor
    · intro h
      rcases Finset.mem_map.mp h with ⟨j,hj,rfl⟩
      refine ⟨rfl,?_⟩
      exact (Finset.mem_filter.mp hj).2
    · rintro ⟨hp,h⟩
      refine Finset.mem_map.mpr ⟨p.1,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,?_⟩
      · rw [← hp]
        exact h
      · exact Prod.ext rfl hp.symm
  have dMem (p : ZMod K × ZMod K) : p ∈ D ↔
      p.2 = p.1+((k+1:ℤ) : ZMod K) ∧
        (↑(f p.2).val : ℤ) - ↑(f p.1).val = (b:ℤ)-B := by
    unfold D
    constructor
    · intro h
      rcases Finset.mem_map.mp h with ⟨j,hj,rfl⟩
      refine ⟨rfl,?_⟩
      exact (Finset.mem_filter.mp hj).2
    · rintro ⟨hp,h⟩
      refine Finset.mem_map.mpr ⟨p.1,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,?_⟩
      · rw [← hp]
        exact h
      · exact Prod.ext rfl hp.symm
  have hU : circularAtomHits f (k*B+b) = A ∪ D := by
    ext p
    simp only [circularAtomHits,Finset.mem_filter,Finset.mem_univ,true_and,
      Finset.mem_union, aMem,dMem]
    have h1 := (f p.1).isLt
    have h2 := (f p.2).isLt
    rw [label_carry_mod_iff (by omega) (by omega) (by omega), modEq_phase_iff, modEq_phase_iff]
  have hDisj : Disjoint A D := by
    apply Finset.disjoint_left.mpr
    intro p ha hd
    have ha' := ((aMem p).mp ha).2
    have hd' := ((dMem p).mp hd).2
    have hb0 : 0 < B := by omega
    omega
  rw [hU, Finset.card_union_of_disjoint hDisj]
  simp [A,D]

theorem circular_atom_count_neg {B K : ℕ} [NeZero K]
    (f : ZMod K → Fin B) (ell : ℤ) :
    (circularAtomHits f (-ell)).card = (circularAtomHits f ell).card := by
  apply Finset.card_equiv (Equiv.prodComm (ZMod K) (ZMod K))
  intro p
  simp only [circularAtomHits,Finset.mem_filter,Finset.mem_univ,true_and,Equiv.prodComm_apply]
  let A := labelCoord (B:ℤ) (p.1.val:ℤ) ((f p.1).val:ℤ)
  let C := labelCoord (B:ℤ) (p.2.val:ℤ) ((f p.2).val:ℤ)
  change (C-A ≡ -ell [ZMOD (B:ℤ)*K]) ↔ (A-C ≡ ell [ZMOD (B:ℤ)*K])
  rw [show C-A = -(A-C) by ring, Int.neg_modEq_neg]

theorem circular_atom_count_zero {B K : ℕ} [NeZero K] (hB : 0 < B)
    (f : ZMod K → Fin B) :
    (circularAtomHits f 0).card = K := by
  have hc := circular_atom_count_as_lags (B:=B) (K:=K) (b:=0) hB f 0
  have hz : (ordinalLagHits f (0:ZMod K) 0).card = K := by
    simp [ordinalLagHits, ZMod.card]
  rw [upper_ordinal_lag_count hB] at hc
  simpa [hz] using hc

#print axioms circular_atom_count_neg
#print axioms circular_atom_count_zero

#print axioms modEq_phase_iff
#print axioms circular_atom_count_as_lags

end CenteredCubeSqrt
