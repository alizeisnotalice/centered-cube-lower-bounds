import SqrtPhysicalCircleCount
import SqrtPeriodicPulse

namespace CenteredCubeSqrt

open scoped BigOperators
open Classical

noncomputable def paperAtomCenter {B K : ℕ} (f : ZMod K → Fin B) (j : ZMod K) : ℝ :=
  ((j.val:ℝ)+((f j).val+1/2)/(B:ℝ))/(K:ℝ)

def atomFineDifference {B K : ℕ} (f : ZMod K → Fin B) (p : ZMod K × ZMod K) : ℤ :=
  labelCoord (B:ℤ) (p.2.val:ℤ) (f p.2).val - labelCoord (B:ℤ) (p.1.val:ℤ) (f p.1).val

def atomDifferenceResidue {B K : ℕ} (f : ZMod K → Fin B)
    (p : ZMod K × ZMod K) : ZMod (B*K) :=
  (atomFineDifference f p : ZMod (B*K))

/-- The integer representative of a fine-grid residue nearest a prescribed
physical lag center. Its choice depends on the shift, but differences still
have their original distinct residues. -/
noncomputable def atomResidueLift {N : ℕ} (shift : ℝ) (r : ZMod N) : ℤ :=
  (r.val:ℤ)-(N:ℤ)*⌊(r.val:ℝ)/N+shift+1/2⌋

theorem atomResidueLift_cast {N : ℕ} [NeZero N] (shift : ℝ) (r : ZMod N) :
    (atomResidueLift shift r : ZMod N) = r := by
  simp [atomResidueLift,Int.cast_sub,Int.cast_mul,Int.cast_natCast]

theorem atomResidueLift_injective {N : ℕ} [NeZero N] (shift : ℝ) :
    Function.Injective (atomResidueLift (N:=N) shift) := by
  intro r t h
  have e := congrArg (fun x : ℤ => (x : ZMod N)) h
  rw [atomResidueLift_cast,atomResidueLift_cast] at e
  exact e

theorem centeredRep_residueLift {N : ℕ} [NeZero N] (shift : ℝ) (r : ZMod N) :
    centeredPeriodRep ((r.val:ℝ)/N+shift) = (atomResidueLift shift r : ℝ)/N+shift := by
  unfold centeredPeriodRep atomResidueLift
  push_cast
  have hN : (N:ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne N)
  field_simp
  ring

/-- Actual physical pair phase is exactly its fine-grid residue lifted near
the prescribed center. In particular all wraps carry no hidden terms. -/
theorem paperAtom_diff_centeredRep {B K : ℕ} [NeZero (B*K)] (f : ZMod K → Fin B)
    (shift : ℝ) (p : ZMod K × ZMod K) :
    centeredPeriodRep (paperAtomCenter f p.2-paperAtomCenter f p.1+shift) =
      (atomResidueLift shift (atomDifferenceResidue f p) : ℝ)/((B:ℝ)*K)+shift := by
  have hN : B*K ≠ 0 := NeZero.ne _
  have hB : (B:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_mul_ne_zero_left hN)
  have hK : (K:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_mul_ne_zero_right hN)
  have eh : paperAtomCenter f p.2-paperAtomCenter f p.1 =
      (atomFineDifference f p : ℝ)/((B:ℝ)*K) := by
    unfold paperAtomCenter
    rw [physical_atom_diff hK hB]
    unfold atomFineDifference labelCoord
    push_cast
    ring
  let r := atomDifferenceResidue f p
  have ecast : (r.val : ZMod (B*K)) = (atomFineDifference f p : ZMod (B*K)) :=
    ZMod.natCast_zmod_val r
  have ecast' : ((r.val:ℤ) : ZMod (B*K)) = (atomFineDifference f p : ZMod (B*K)) := by
    rw [Int.cast_natCast]
    exact ecast
  obtain ⟨z,hz⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp ecast'
  have hz' : (atomFineDifference f p : ℝ) = r.val+(B:ℝ)*K*(z:ℝ) := by
    have hz'' : (atomFineDifference f p : ℝ)-(r.val:ℝ) = ((B:ℝ)*K)*(z:ℝ) := by
      exact_mod_cast hz
    linarith
  rw [eh,hz']
  have e' : ((r.val:ℝ)+(B:ℝ)*K*z)/((B:ℝ)*K)+shift =
      ((r.val:ℝ)/((B:ℝ)*K)+shift)+(z:ℤ) := by field_simp; ring
  rw [e',centeredPeriodRep_int]
  simpa only [Nat.cast_mul] using centeredRep_residueLift shift r

theorem circular_atom_hits_eq_residue_fiber {B K : ℕ} [NeZero K]
    (f : ZMod K → Fin B) (ell : ℤ) :
    circularAtomHits f ell =
      Finset.univ.filter fun p => atomDifferenceResidue f p = (ell : ZMod (B*K)) := by
  ext p
  simp only [circularAtomHits,Finset.mem_filter,Finset.mem_univ,true_and,
    atomDifferenceResidue,atomFineDifference, Int.modEq_iff_dvd,
    ZMod.intCast_eq_intCast_iff_dvd_sub, Nat.cast_mul]

/-- Exact grouped sum for any kernel on the physical fine-grid residues. -/
theorem sum_atom_difference_residue_kernel {B K : ℕ} [NeZero K] [NeZero (B*K)]
    (f : ZMod K → Fin B) (shift : ℝ) (kernel : ZMod (B*K) → ℝ) :
    (∑ p : ZMod K × ZMod K, kernel (atomDifferenceResidue f p)) =
      ∑ r : ZMod (B*K),
        ((circularAtomHits f (atomResidueLift shift r)).card : ℝ) * kernel r := by
  rw [← Finset.sum_fiberwise' Finset.univ (atomDifferenceResidue f) kernel]
  apply Finset.sum_congr rfl
  intro r _
  rw [circular_atom_hits_eq_residue_fiber, atomResidueLift_cast]
  simp only [Finset.sum_const,nsmul_eq_mul]

#print axioms sum_atom_difference_residue_kernel

#print axioms atomResidueLift_injective
#print axioms paperAtom_diff_centeredRep
#print axioms circular_atom_hits_eq_residue_fiber

end CenteredCubeSqrt
