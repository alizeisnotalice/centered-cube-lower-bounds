import SqrtRawPrimitive
import SqrtOrdinalCyclicLabels

namespace CenteredCubeSqrt
open Set
open scoped BigOperators
set_option maxHeartbeats 1800000
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem raw_regular_pair_sum {b d : ℕ} [NeZero (2^d-1)] (hd : 0<d)
    (g : (LabelField d)ˣ) (hg : orderOf g=2^d-1) {t : Fin b → LabelField d}
    (ht : LinearIndependent (ZMod 2) t) (k : ZMod (2^d-1))
    (hk : (phaseState hd g hg k : LabelField d) ≠ 1)
    (hk' : (phaseState hd g hg k : LabelField d) ∉ labelRatioSet t)
    (hdim : 2*b≤d) (w : Fin (2^b) × Fin (2^b) → ℝ) :
    let f := ordinalPhaseLabel hd g hg t
    let B := (2:ℝ)^b
    let q := (2:ℝ)^d
    (∑ j : ZMod (2^d-1), w (f j,f (j+k))) =
      (q/B^2)*(∑ p : Fin (2^b) × Fin (2^b), w p)-w (0,0) := by
  classical
  let f := ordinalPhaseLabel hd g hg t
  let F (j : ZMod (2^d-1)) := (f j, f (j+k))
  let B := (2:ℝ)^b
  let q := (2:ℝ)^d
  let u := (2^d/(2^b)^2:ℕ)
  have E : ((u:ℕ):ℝ)=q/B^2 := by
    have hdiv : (2^b)^2 ∣ (2:ℕ)^d := by rw [←pow_mul, mul_comm b 2]; exact pow_dvd_pow 2 hdim
    unfold u B q
    rw [Nat.cast_div hdiv (by positivity)]
    push_cast
    rfl
  have hu : 1≤u := by
    have hq : 0<q := by dsimp [q]; positivity
    have hB : 0<B := by dsimp [B]; positivity
    have hpos : 0<(u:ℝ) := by rw [E]; positivity
    exact Nat.succ_le_of_lt (by exact_mod_cast hpos)
  change (∑ j : ZMod (2^d-1), w (F j))=(q/B^2)*(∑ p : Fin (2^b) × Fin (2^b),w p)-w (0,0)
  rw [←Finset.sum_fiberwise' Finset.univ F w, ←E]
  have hcnt (p : Fin (2^b) × Fin (2^b)) :
    ((Finset.univ.filter fun j => F j=p).card:ℝ) =
      (u:ℝ)-if p=(0,0) then 1 else 0 := by
    have he : (Finset.univ.filter fun j => F j=p).card =
      Nat.card {j : ZMod (2^d-1) // f j=p.1 ∧ f (j+k)=p.2} := by
      rw [Nat.card_eq_fintype_card,Fintype.card_subtype]
      congr 1
    rw [he,regular_ordinal_cyclic_label_count hd g hg ht k hk hk' hdim]
    by_cases hp : p=(0,0)
    · subst p
      simp only [Fin.val_zero,and_self,ite_true]
      rw [Nat.cast_sub hu]
      rfl
    · have hp' : ¬(p.1.val=0 ∧ p.2.val=0) := by
        intro h
        exact hp (Prod.ext (Fin.ext h.1) (Fin.ext h.2))
      rw [ite_eq_right hp',ite_eq_right hp,Nat.sub_zero,sub_zero]
  simp_rw [Finset.sum_const,nsmul_eq_mul,hcnt,sub_mul]
  rw [Finset.sum_sub_distrib,←Finset.mul_sum]
  have h (p : Fin (2^b) × Fin (2^b)) :
      (if p=(0,0) then (1:ℝ) else 0)*w p = if p=(0,0) then w (0,0) else 0 := by
    split <;> rename_i hp
    · subst p
      simp
    · simp
  simp_rw [h]
  simp

#print axioms raw_regular_pair_sum
end CenteredCubeSqrt
