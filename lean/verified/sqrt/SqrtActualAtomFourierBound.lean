import SqrtActualPhaseWeights
import SqrtAtomResidue

namespace CenteredCubeSqrt
open scoped BigOperators
open Complex
set_option maxHeartbeats 330000

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

noncomputable def coarsePhase {K : ℕ} [NeZero K] (m : ℕ) (j : ZMod K) : ℂ :=
  Complex.exp (2*(Real.pi:ℂ)*I*(m:ℂ)*(j.val:ℂ)/(K:ℂ))

theorem coarsePhase_eq_stdAddChar {K : ℕ} [NeZero K] (m : ℕ) (j : ZMod K) :
    coarsePhase m j = ZMod.stdAddChar ((m:ZMod K)*j) := by
  have hc : (((m*j.val:ℕ):ℤ):ZMod K) = (m:ZMod K)*j := by
    push_cast
    rw [ZMod.natCast_zmod_val]
  rw [←hc, ZMod.stdAddChar_coe]
  unfold coarsePhase
  push_cast
  ring

theorem coarsePhase_norm {K : ℕ} [NeZero K] (m : ℕ) (j : ZMod K) :
    ‖coarsePhase m j‖=1 := by
  rw [coarsePhase_eq_stdAddChar,ZMod.stdAddChar_apply,Circle.norm_coe]

theorem modFrequency_cancel {K : ℕ} [NeZero K] (x : ZMod K) (hx : x≠0) :
    (∑ j : ZMod K, ZMod.stdAddChar (x*j)) = 0 := by
  classical
  have hNZ : ZMod.stdAddChar x ≠ 1 := fun h =>
    hx (ZMod.injective_stdAddChar (h.trans (AddChar.map_zero_eq_one ZMod.stdAddChar).symm))
  have h : ZMod.stdAddChar x * (∑ j : ZMod K, ZMod.stdAddChar (x*j)) =
      ∑ j : ZMod K, ZMod.stdAddChar (x*j) := by
    rw [Finset.mul_sum]
    refine Fintype.sum_equiv (Equiv.addLeft (1:ZMod K)) _ _ (fun j => ?_)
    have hj : Equiv.addLeft (1:ZMod K) j = 1+j := rfl
    simp only [hj,mul_add,mul_one,AddChar.map_add_eq_mul]
  exact eq_zero_of_mul_eq_self_left hNZ h

theorem coarsePhase_cancel {K : ℕ} [NeZero K] {m : ℕ} (hm0 : 0<m) (hmK : m<K) :
    (∑ j : ZMod K, coarsePhase m j) = 0 := by
  have hx : (m:ZMod K) ≠ 0 := by
    intro h
    have v := congrArg (ZMod.val (n:=K)) h
    rw [ZMod.val_natCast_of_lt hmK,ZMod.val_zero] at v
    exact hm0.ne' v
  simp_rw [coarsePhase_eq_stdAddChar]
  exact modFrequency_cancel (m:ZMod K) hx

theorem actual_weighted_atom_phase_bound {b d : ℕ} [NeZero (2^d-1)] (hd : 0<d)
    (g : (LabelField d)ˣ) (hg : orderOf g=2^d-1)
    (t : Fin b → LabelField d) (ht : ∀ i,t i ≠ 0) {m : ℕ} (hm0 : 0<m) (hmK : m<2^d-1) :
    ‖∑ j : ZMod (2^d-1), coarsePhase m j*(atomPhaseOffset (ordinalPhaseLabel hd g hg t) j:ℂ)‖ ≤
      ((1-1/(2:ℝ)^b)/2)*Real.sqrt ((2^d:ℕ):ℝ) := by
  classical
  let w (i : Fin b) := phaseBitWeight i
  let A (i : Fin b) := ∑ j : ZMod (2^d-1), coarsePhase m j *
    traceFieldCharacter (t i) (phaseState hd g hg j : LabelField d)
  have he (j : ZMod (2^d-1)) := exact_phaseOffset_character_expansion hd g hg t j
  simp_rw [he,mul_neg,Finset.sum_neg_distrib,norm_neg,Finset.mul_sum]
  rw [Finset.sum_comm]
  have e : (∑ i : Fin b,∑ j : ZMod (2^d-1),
      coarsePhase m j *((phaseBitWeight i:ℂ) * traceFieldCharacter (t i) (phaseState hd g hg j : LabelField d))) =
    ∑ i : Fin b, (w i:ℂ)*A i := by
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [A]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    unfold w
    ring
  rw [e]
  have hA (i : Fin b) : ‖A i‖ = Real.sqrt ((2^d:ℕ):ℝ) := by
    have e : ‖A i‖^2 = ((2^d:ℕ):ℝ) := by
      rw [←actual_paperGauss_norm_sq hd g hg hm0 hmK (ht i),paperGauss_as_exp_trace_sum]
      rfl
    rw [←e,Real.sqrt_sq (norm_nonneg _)]
  refine (norm_sum_le _ _).trans ?_
  have eW (i : Fin b) : |w i|=w i := abs_of_nonneg (by unfold w phaseBitWeight; positivity)
  simp_rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,hA,eW]
  rw [←Finset.sum_mul]
  exact le_of_eq (congrArg (fun x => x*Real.sqrt ((2^d:ℕ):ℝ)) (phaseBitWeight_sum b))

#print axioms coarsePhase_cancel
#print axioms actual_weighted_atom_phase_bound

end CenteredCubeSqrt
