import SqrtPhysicalPaperCounts
import SqrtLocalResidueBudget

namespace CenteredCubeSqrt

open scoped BigOperators
open Classical

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem atomResidueLift_zero_zero {N : ℕ} [NeZero N] :
    atomResidueLift (N:=N) 0 0 = 0 := by
  have hf : ⌊(1/2:ℝ)⌋=(0:ℤ) := Int.floor_eq_iff.mpr (by norm_num)
  unfold atomResidueLift
  rw [ZMod.val_zero]
  simp only [Nat.cast_zero,zero_div,zero_add,hf,mul_zero,sub_zero]

/-- Total phase count normalized by the number of atoms. -/
noncomputable def atomWeight {B K : ℕ} [NeZero K] [NeZero (B*K)]
    (f : ZMod K → Fin B) (shift : ℝ) (r : ZMod (B*K)) : ℝ :=
  ((circularAtomHits f (atomResidueLift shift r)).card : ℝ)/(K:ℝ)

theorem atomWeight_zero {B K : ℕ} [NeZero K] [NeZero (B*K)] (hB : 0 < B)
    (f : ZMod K → Fin B) :
    atomWeight f 0 0 = 1 := by
  have hK : (K:ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne K)
  rw [atomWeight, atomResidueLift_zero_zero, circular_atom_count_zero hB,div_self hK]

theorem actual_atom_weight_small {b d : ℕ} [NeZero (2^d-1)]
    [NeZero (2^b*(2^d-1))] (hd : 0 < d) (g : (LabelField d)ˣ)
    (hg : orderOf g = 2^d-1) {t : Fin b → LabelField d}
    (ht : LinearIndependent (ZMod 2) t) (hdim : 2*b ≤ d)
    (h1 : (phaseState hd g hg 1 : LabelField d) ≠ 1)
    (h1' : (phaseState hd g hg 1 : LabelField d) ∉ labelRatioSet t)
    {v R : ℝ} (hv : 0 < v) (hR : 0 ≤ R ∧ R < v) (hBv : ((2^b:ℕ):ℝ) ≤ 2*v)
    {r : ZMod (2^b*(2^d-1))} (hr : r ≠ 0)
    (hwin : r ∈ physicalWindowResidues (B:=2^b) (K:=2^d-1) v R 0) :
    0 ≤ atomWeight (ordinalPhaseLabel hd g hg t) 0 r ∧
    atomWeight (ordinalPhaseLabel hd g hg t) 0 r ≤ 4*R/(((2^b:ℕ):ℝ)^2) := by
  let K : ℕ := 2^d-1
  let B : ℕ := 2^b
  let ell := atomResidueLift 0 r
  have hB : (0:ℝ)<B := by dsimp [B]; positivity
  have hK : (0:ℝ)<K := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne K)
  have hC : 0 < (K:ℝ)*v := by positivity
  have hph : |(ell:ℝ)/((B:ℝ)*K)| ≤ R/((K:ℝ)*v) := by
    have e := (Finset.mem_filter.mp hwin).2
    change |((K:ℝ)*v)*((ell:ℝ)/((B:ℝ)*K)+0)| ≤ R at e
    rw [add_zero,abs_mul,abs_of_pos hC] at e
    exact (le_div_iff₀ hC).mpr (by rwa [mul_comm])
  have hel0 : ell≠0 := by
    intro e
    have ee := atomResidueLift_cast (N:=2^b*(2^d-1)) 0 r
    change ((ell:ℤ) : ZMod (2^b*(2^d-1))) = r at ee
    rw [e, Int.cast_zero] at ee
    exact hr ee.symm
  have habs : (ell.natAbs:ℝ)=|(ell:ℝ)| := by rw [Nat.cast_natAbs,Int.cast_abs]
  have hel : ell.natAbs < B := by
    have hh := local_same_direction_small hB hK hv hR.2 hph
    rw [← habs] at hh
    exact_mod_cast hh
  have hfin : |(ell:ℝ)| ≤ 2*R := by
    have ee := local_fine_window_pullback hB hK hv hR.1 hBv (x:=0) ell (by simpa using hph)
    simpa using ee
  have count := manuscript_physical_count_small_int (ell:=ell) hd g hg ht hdim h1 h1' hel0 hel
  have hA : ((2^(d-2*b):ℕ):ℝ) = ((2^d:ℕ):ℝ)/(B:ℝ)^2 := by
    have hN : (2:ℕ)^d = (2^(d-2*b):ℕ)*B^2 := by
      dsimp [B]
      rw [←pow_mul,Nat.mul_comm b 2,←pow_add,Nat.sub_add_cancel hdim]
    apply (eq_div_iff (by positivity : (B:ℝ)^2 ≠ 0)).2
    exact_mod_cast hN.symm
  have hqK : ((2^d:ℕ):ℝ) ≤ 2*(K:ℝ) := by
    have hkN : 0<K := Nat.pos_of_ne_zero (NeZero.ne K)
    have qK : (2:ℕ)^d=K+1 := by dsimp [K]; rw [Nat.sub_add_cancel Nat.one_le_two_pow]
    rw [qK]
    push_cast
    have h1K : (1:ℝ) ≤ K := by exact_mod_cast hkN
    linarith
  unfold atomWeight
  change 0 ≤ (((circularAtomHits (ordinalPhaseLabel hd g hg t) ell).card:ℕ):ℝ)/(K:ℝ) ∧
    _ ≤ 4*R/(B:ℝ)^2
  rw [count,Nat.cast_mul,hA]
  have hb2 : 0 < (B:ℝ)^2 := by positivity
  rw [habs]
  constructor
  · positivity
  · apply (div_le_iff₀ hK).2
    have hh : ((2^d:ℕ):ℝ)/(B:ℝ)^2 ≤ (2*(K:ℝ))/(B:ℝ)^2 :=
      div_le_div_of_nonneg_right hqK hb2.le
    calc
      _ ≤ (2*R)*((2*(K:ℝ))/(B:ℝ)^2) := mul_le_mul hfin hh (div_nonneg (by positivity) hb2.le) (by linarith [hR.1])
      _ = _ := by ring

theorem field_card_per_period_bound (d : ℕ) [NeZero (2^d-1)] :
    ((2^d:ℕ):ℝ) ≤ 2*(((2^d-1:ℕ):ℝ)) := by
  let K : ℕ := 2^d-1
  have hkN : 0<K := Nat.pos_of_ne_zero (NeZero.ne K)
  have qK : (2:ℕ)^d=K+1 := by dsimp [K]; rw [Nat.sub_add_cancel Nat.one_le_two_pow]
  change ((2^d:ℕ):ℝ) ≤ 2*(K:ℝ)
  rw [qK]
  push_cast
  have h1K : (1:ℝ) ≤ K := by exact_mod_cast hkN
  linarith

theorem actual_atom_weight_mirror {b d : ℕ} [NeZero (2^d-1)]
    [NeZero (2^b*(2^d-1))] (hd : 0 < d) (g : (LabelField d)ˣ)
    (hg : orderOf g = 2^d-1) {t : Fin b → LabelField d}
    (ht : LinearIndependent (ZMod 2) t) (hdim : 2*b ≤ d)
    {v R L0 : ℝ} (hv : 0 < v) (hR : 0 ≤ R ∧ R < v)
    (hSafe : ∀ k : ℤ, |(k:ℝ)-(((2^d-1:ℕ):ℝ))*L0| < 2 →
      (phaseState hd g hg (k:ZMod (2^d-1)) : LabelField d) ≠ 1 ∧
      (phaseState hd g hg (k:ZMod (2^d-1)) : LabelField d) ∉ labelRatioSet t)
    {r : ZMod (2^b*(2^d-1))}
    (hwin : r ∈ physicalWindowResidues (B:=2^b) (K:=2^d-1) v R (-L0)) :
    0 ≤ atomWeight (ordinalPhaseLabel hd g hg t) (-L0) r ∧
    atomWeight (ordinalPhaseLabel hd g hg t) (-L0) r ≤ 2/((2^b:ℕ):ℝ) := by
  let K : ℕ := 2^d-1
  let B : ℕ := 2^b
  let ell := atomResidueLift (-L0) r
  have hBN : 0 < B := by dsimp [B]; positivity
  have hB : 0 < (B:ℝ) := by exact_mod_cast hBN
  have hKi : 0 < K := Nat.pos_of_ne_zero (NeZero.ne K)
  have hK : 0 < (K:ℝ) := by exact_mod_cast hKi
  have hC : 0 < (K:ℝ)*v := by positivity
  have hp : |(ell:ℝ)/((B:ℝ)*K)-L0| ≤ R/((K:ℝ)*v) := by
    have h := (Finset.mem_filter.mp hwin).2
    change |((K:ℝ)*v)*((ell:ℝ)/((B:ℝ)*K)+(-L0))| ≤ R at h
    rw [← sub_eq_add_neg,abs_mul,abs_of_pos hC] at h
    exact (le_div_iff₀ hC).mpr (by rwa [mul_comm])
  let k := ell/(B:ℤ)
  let rem := ell%(B:ℤ)
  have hr₀ : 0 ≤ rem := Int.emod_nonneg _ (by exact_mod_cast hBN.ne')
  have hr₁ : rem < B := Int.emod_lt_of_pos _ (by exact_mod_cast hBN)
  let b0 := rem.toNat
  have hrc : (b0:ℤ)=rem := Int.toNat_of_nonneg hr₀
  have hb0 : b0 < B := by
    rw [← hrc] at hr₁
    exact_mod_cast hr₁
  have eInt : ell = k*(B:ℤ)+(b0:ℤ) := by rw [hrc]; exact (Int.ediv_mul_add_emod ell B).symm
  have eReal : (ell:ℝ)=(B:ℝ)*(k:ℝ)+b0 := by
    rw [mul_comm (B:ℝ)]
    exact_mod_cast eInt
  have hrem : (0:ℝ) ≤ b0 ∧ (b0:ℝ)<B := ⟨by positivity,by exact_mod_cast hb0⟩
  obtain ⟨hnear1,hnear2⟩ := local_both_mirror_carries_near hB hK hv hR hrem eReal hp
  have hSafe1 := hSafe k hnear1
  have hSafe2 := hSafe (k+1) (by simpa only [Int.cast_add,Int.cast_one] using hnear2)
  have count := manuscript_physical_count_regular hd g hg ht hdim k hb0 hSafe1.1 hSafe1.2
      hSafe2.1 hSafe2.2
  have count' : (circularAtomHits (ordinalPhaseLabel hd g hg t) ell).card =
      2^d/B - if b0=0 then 1 else 0 := by
    rw [eInt]
    exact count
  change 0 ≤ (((circularAtomHits (ordinalPhaseLabel hd g hg t) ell).card:ℕ):ℝ)/(K:ℝ) ∧
    (((circularAtomHits (ordinalPhaseLabel hd g hg t) ell).card:ℕ):ℝ)/(K:ℝ) ≤ 2/(B:ℝ)
  rw [count']
  constructor
  · positivity
  · have hn : (2^d:ℕ)/B - (if b0=0 then 1 else 0) ≤ (2^d:ℕ)/B := Nat.sub_le _ _
    have hn' : (((2^d:ℕ)/B - (if b0=0 then 1 else 0):ℕ):ℝ) ≤ (((2^d:ℕ)/B:ℕ):ℝ) := by
      exact_mod_cast hn
    have divBound : (((2^d:ℕ)/B:ℕ):ℝ) ≤ ((2^d:ℕ):ℝ)/(B:ℝ) := by
      apply (le_div_iff₀ hB).mpr
      exact_mod_cast Nat.div_mul_le_self (2^d) B
    apply (div_le_iff₀ hK).2
    calc
      _ ≤ ((2^d:ℕ):ℝ)/(B:ℝ) := hn'.trans divBound
      _ ≤ (2*(K:ℝ))/(B:ℝ) := div_le_div_of_nonneg_right (field_card_per_period_bound d) hB.le
      _ = _ := by ring

#print axioms actual_atom_weight_mirror

#print axioms atomWeight_zero
#print axioms actual_atom_weight_small

end CenteredCubeSqrt
