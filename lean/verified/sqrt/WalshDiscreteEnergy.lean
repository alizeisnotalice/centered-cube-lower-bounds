import WalshBalanced

namespace CenteredCubeSqrt
open scoped BigOperators
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

noncomputable def walshRun : (b : ℕ) → (Fin b → Bool) → ℕ
| 0, _ => 1
| b+1, a => if Fin.init a = (fun _ => false) then 2^b else walshRun b (Fin.init a)

theorem reflected_real_square_sum (N : ℕ) :
    (∑ j ∈ Finset.range N, ((N:ℝ)-j)^2) =
       (∑ j ∈ Finset.range N, (j:ℝ)^2) + (N:ℝ)^2 := by
  have hr := Finset.sum_range_reflect (fun j : ℕ => ((j:ℝ)+1)^2) N
  have e : (∑ j ∈ Finset.range N, ((N:ℝ)-j)^2) =
      ∑ j ∈ Finset.range N, (((N-1-j:ℕ):ℝ)+1)^2 := by
    apply Finset.sum_congr rfl
    intro j hj
    have h : j<N := Finset.mem_range.mp hj
    have h' : N-1-j+1+j=N := by omega
    have hh := congrArg (fun k : ℕ => (k:ℝ)) h'
    push_cast at hh
    rw [show (N:ℝ)-j=(((N-1-j:ℕ):ℝ)+1) by linarith]
  rw [e, hr]
  have h := Finset.sum_range_succ' (fun j : ℕ => (j:ℝ)^2) N
  rw [Finset.sum_range_succ] at h
  push_cast at h
  simpa using h.symm

theorem walshDiscreteEnergy_top {b : ℕ} (a : Fin (b+1) → Bool)
    (h : Fin.init a = fun _ => false) (hlt : a (Fin.last b)=true) :
    walshDiscreteEnergy a = (2*((2:ℝ)^b)^3+(2:ℝ)^b)/3 := by
  unfold walshDiscreteEnergy
  rw [show (2:ℕ)^(b+1)=2^b+2^b by rw [pow_succ]; omega, Finset.sum_range_add]
  have h₁ : (∑ j ∈ Finset.range (2^b), (walshPrefix a j)^2) =
      ∑ j ∈ Finset.range (2^b), (j:ℝ)^2 := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [walshPrefix_succ_first_half a j (Finset.mem_range.mp hj).le, h, walshPrefix_zero]
  have h₂ : (∑ j ∈ Finset.range (2^b), (walshPrefix a (2^b+j))^2) =
      ∑ j ∈ Finset.range (2^b), (((2^b:ℕ):ℝ)-j)^2 := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [walshPrefix_succ_second_half a j (Finset.mem_range.mp hj).le,
      h, hlt, walshPrefix_zero, walshPrefix_zero]
    norm_num [bitCharacter, show (1:ZMod 2).val=1 from rfl, sub_eq_add_neg]
  rw [h₁,h₂,reflected_real_square_sum,sum_range_real_squares]
  push_cast
  ring

theorem walshDiscreteEnergy_exact {b : ℕ} (a : Fin b → Bool) (ha : a ≠ fun _ => false) :
    walshDiscreteEnergy a = (2:ℝ)^b * ((walshRun b a : ℝ)^2/3 + 1/6) := by
  induction b with
  | zero =>
    exact (ha (funext fun i => Fin.elim0 i)).elim
  | succ b ih =>
    by_cases h : Fin.init a = fun _ => false
    · have hlt : a (Fin.last b)=true := by
        cases e : a (Fin.last b)
        · exact (ha (walsh_init_last_determine h e)).elim
        · rfl
      rw [walshDiscreteEnergy_top a h hlt, walshRun, if_pos h, pow_succ]
      push_cast
      ring
    · rw [walshDiscreteEnergy_repeat a h, ih _ h, walshRun, if_neg h, pow_succ]
      ring

#print axioms walshDiscreteEnergy_exact
end CenteredCubeSqrt
