import OrdinalWalsh
import SqrtRawRegularPair
import Mathlib.Tactic.Ring

namespace CenteredCubeSqrt
open Classical
open scoped BigOperators
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem defective_ordinal_walsh_sum {b d : ℕ} [NeZero (2^d-1)] (hd : 0<d)
    (hb : 0<b) (hdim : 2*b≤d)
    (g : (LabelField d)ˣ) (hg : orderOf g=2^d-1) {t : Fin b → LabelField d}
    (ht : LinearIndependent (ZMod 2) t) (k : ZMod (2^d-1))
    (hk : (phaseState hd g hg k : LabelField d) ≠ 1)
    (hk' : (phaseState hd g hg k : LabelField d) ∈ labelRatioSet t)
    (hS : MultiplicativeSidon {x : LabelField d | x ∈ labelSpace t ∧ x ≠ 0})
    (a c : NonzeroBinary b)
    (hmatch : labelValue t a = (phaseState hd g hg k : LabelField d)*labelValue t c)
    (w : Fin (2^b) × Fin (2^b) → ℝ) :
    let f := ordinalPhaseLabel hd g hg t
    let B := (2:ℝ)^b
    let q := (2:ℝ)^d
    (∑ j : ZMod (2^d-1), w (f j,f (j+k))) =
      (q/B^2)*((∑ p : Fin (2^b) × Fin (2^b), w p) +
        (∑ p : Fin (2^b) × Fin (2^b), ordinalWalsh a p.1 * ordinalWalsh c p.2 * w p))
        - w (0,0) := by
  classical
  let f := ordinalPhaseLabel hd g hg t
  let F (j : ZMod (2^d-1)) := (f j, f (j+k))
  let B := (2:ℝ)^b
  let q := (2:ℝ)^d
  change (∑ j : ZMod (2^d-1), w (F j)) = _
  rw [←Finset.sum_fiberwise' Finset.univ F w]
  have hcnt (p : Fin (2^b) × Fin (2^b)) :
    ((Finset.univ.filter fun j => F j=p).card:ℝ) =
      q/B^2*(1 + ordinalWalsh a p.1 * ordinalWalsh c p.2)
      - if p=(0,0) then 1 else 0 := by
    have he : (Finset.univ.filter fun j => F j=p).card =
      Nat.card {j : ZMod (2^d-1) // f j=p.1 ∧ f (j+k)=p.2} := by
      rw [Nat.card_eq_fintype_card,Fintype.card_subtype]
      congr 1
    rw [he, defective_ordinal_walsh_count hd hb hdim g hg ht k hk hk' hS a c hmatch]
  simp_rw [Finset.sum_const, nsmul_eq_mul, hcnt, sub_mul, mul_assoc, add_mul, one_mul,
    Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_add_distrib]
  have e (p : Fin (2^b) × Fin (2^b)) :
      (if p=(0,0) then (1:ℝ) else 0)*w p = if p=(0,0) then w (0,0) else 0 := by
    by_cases hp : p=(0,0) <;> simp [hp]
  simp_rw [e]
  simp [mul_assoc, q, B]

#print axioms defective_ordinal_walsh_sum
end CenteredCubeSqrt
