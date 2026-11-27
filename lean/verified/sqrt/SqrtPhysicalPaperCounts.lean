import SqrtOrdinalCyclicLabels
import SqrtPhysicalCircleCount

namespace CenteredCubeSqrt

open Classical
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem actual_regular_ordinal_fiber {b d : ℕ} [NeZero (2^d-1)] (hd : 0 < d)
    (g : (LabelField d)ˣ) (hg : orderOf g = 2^d-1) {t : Fin b → LabelField d}
    (ht : LinearIndependent (ZMod 2) t) (k : ZMod (2^d-1))
    (hk : (phaseState hd g hg k : LabelField d) ≠ 1)
    (hk' : (phaseState hd g hg k : LabelField d) ∉ labelRatioSet t)
    (hdim : 2*b ≤ d) {y z : ℕ} (hy : y < 2^b) (hz : z < 2^b) :
    (ordinalPairFiber (ordinalPhaseLabel hd g hg t) k y z).card =
      2^(d-2*b) - if y=0 ∧ z=0 then 1 else 0 := by
  have count := regular_ordinal_cyclic_label_count hd g hg ht k hk hk' hdim ⟨y,hy⟩ ⟨z,hz⟩
  have e : ordinalPairFiber (ordinalPhaseLabel hd g hg t) k y z =
      Finset.univ.filter (fun j => ordinalPhaseLabel hd g hg t j = ⟨y,hy⟩ ∧
        ordinalPhaseLabel hd g hg t (j+k) = ⟨z,hz⟩) := by
    ext j
    simp only [ordinalPairFiber,Finset.mem_filter,Finset.mem_univ,true_and]
    exact and_congr ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩
      ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩
  rw [e, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card, count]
  rw [← pow_mul, Nat.mul_comm b 2, two_power_div_of_le hdim]

/-- Exact paperphysicalcount for two regular/nonzero coarse cells. The count
is over the actual primitive trace sequence and integer fine atom positions. -/
theorem manuscript_physical_count_regular {b d : ℕ} [NeZero (2^d-1)] (hd : 0 < d)
    (g : (LabelField d)ˣ) (hg : orderOf g = 2^d-1) {t : Fin b → LabelField d}
    (ht : LinearIndependent (ZMod 2) t) (hdim : 2*b ≤ d)
    (k : ℤ) {r : ℕ} (hr : r < 2^b)
    (hk : (phaseState hd g hg (k : ZMod (2^d-1)) : LabelField d) ≠ 1)
    (hk' : (phaseState hd g hg (k : ZMod (2^d-1)) : LabelField d) ∉ labelRatioSet t)
    (hl : (phaseState hd g hg ((k+1:ℤ) : ZMod (2^d-1)) : LabelField d) ≠ 1)
    (hl' : (phaseState hd g hg ((k+1:ℤ) : ZMod (2^d-1)) : LabelField d) ∉ labelRatioSet t) :
    (circularAtomHits (ordinalPhaseLabel hd g hg t) (k*(2^b:ℕ)+r)).card =
      2^d/2^b - if r=0 then 1 else 0 := by
  rw [circular_atom_count_as_lags hr]
  have hQ : (2:ℕ)^d = (2^b)*(2^b)*2^(d-2*b) := by
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  exact two_regular_ordinal_lag_count hr hQ (by positivity) _ _ _
    (fun _ _ hy hz => actual_regular_ordinal_fiber hd g hg ht _ hk hk' hdim hy hz)
    (fun _ _ hy hz => actual_regular_ordinal_fiber hd g hg ht _ hl hl' hdim hy hz)

/-- Exact tiny positive difference, with only the adjacent regular
carry contributing. Negative differences use the pair-swap identity. -/
theorem manuscript_physical_count_small_nat {b d : ℕ} [NeZero (2^d-1)] (hd : 0 < d)
    (g : (LabelField d)ˣ) (hg : orderOf g = 2^d-1) {t : Fin b → LabelField d}
    (ht : LinearIndependent (ZMod 2) t) (hdim : 2*b ≤ d)
    (h1 : (phaseState hd g hg 1 : LabelField d) ≠ 1)
    (h1' : (phaseState hd g hg 1 : LabelField d) ∉ labelRatioSet t)
    {r : ℕ} (hr0 : 0 < r) (hr : r < 2^b) :
    (circularAtomHits (ordinalPhaseLabel hd g hg t) (r:ℤ)).card =
      r*2^(d-2*b) := by
  let f := ordinalPhaseLabel hd g hg t
  have carry := circular_atom_count_as_lags hr f 0
  simp only [zero_mul,zero_add,Int.cast_zero,Int.cast_one] at carry
  change (circularAtomHits f (r:ℤ)).card = _
  rw [carry]
  have hzero : (ordinalLagHits f (0:ZMod (2^d-1)) r).card = 0 := by
    have hne : (r:ℤ) ≠ 0 := by exact_mod_cast hr0.ne'
    simp [ordinalLagHits,Ne.symm hne]
  rw [hzero, zero_add, upper_ordinal_lag_count hr]
  rw [Nat.mul_comm r]
  apply physical_count_small_positive
  intro z hz
  have hz' := Finset.mem_range.mp hz
  rw [actual_regular_ordinal_fiber hd g hg ht 1 h1 h1' hdim
    (show z+2^b-r < 2^b by omega) (show z<2^b by omega)]
  have hnot : ¬(z+2^b-r=0 ∧ z=0) := by omega
  simp [hnot]

/-- Symmetric tiny-shift count with the exact paper coefficient. -/
theorem manuscript_physical_count_small_int {b d : ℕ} [NeZero (2^d-1)] (hd : 0 < d)
    (g : (LabelField d)ˣ) (hg : orderOf g = 2^d-1) {t : Fin b → LabelField d}
    (ht : LinearIndependent (ZMod 2) t) (hdim : 2*b ≤ d)
    (h1 : (phaseState hd g hg 1 : LabelField d) ≠ 1)
    (h1' : (phaseState hd g hg 1 : LabelField d) ∉ labelRatioSet t)
    {ell : ℤ} (hell0 : ell ≠ 0) (hell : ell.natAbs < 2^b) :
    (circularAtomHits (ordinalPhaseLabel hd g hg t) ell).card =
      ell.natAbs*2^(d-2*b) := by
  have hpos : 0 < ell.natAbs := Int.natAbs_pos.mpr hell0
  have e := manuscript_physical_count_small_nat hd g hg ht hdim h1 h1' hpos hell
  by_cases hn : 0 ≤ ell
  · rwa [Int.natAbs_of_nonneg hn] at e
  · have he : (ell.natAbs:ℤ) = -ell := by omega
    rwa [he,circular_atom_count_neg] at e

#print axioms manuscript_physical_count_small_nat
#print axioms manuscript_physical_count_small_int

#print axioms actual_regular_ordinal_fiber
#print axioms manuscript_physical_count_regular

end CenteredCubeSqrt
