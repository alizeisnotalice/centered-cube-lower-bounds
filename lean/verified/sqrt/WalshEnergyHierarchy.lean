import WalshContinuousEnergy

namespace CenteredCubeSqrt
open MeasureTheory Set Classical
open scoped Interval BigOperators
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem walshRun_le_half {b : ℕ} (a : Fin (b+1) → Bool) :
    walshRun (b+1) a ≤ 2^b := by
  induction b with
  | zero =>
    rw [walshRun]
    split <;> simp [walshRun]
  | succ b ih =>
    rw [walshRun]
    split
    · exact le_rfl
    · have hh := ih (Fin.init a)
      exact hh.trans (by rw [pow_succ]; omega)

theorem walshRun_lower_layer {b : ℕ} (a : Fin (b+1) → Bool)
    (h : Fin.init a ≠ fun _ => false) :
    walshRun (b+1) a*4 ≤ 2^(b+1) := by
  cases b with
  | zero =>
    exact (h (funext fun i => Fin.elim0 i)).elim
  | succ b =>
    rw [walshRun, ite_eq_right h]
    have hh := walshRun_le_half (Fin.init a)
    rw [pow_succ,pow_succ]
    omega

theorem walsh_highest_unique {b : ℕ} (a c : NonzeroBinary (b+1))
    (ha : Fin.init a.1 = fun _ => false) (hc : Fin.init c.1 = fun _ => false) : a=c := by
  have hbit (x : NonzeroBinary (b+1)) (hx : Fin.init x.1 = fun _ => false) : x.1 (Fin.last b)=true := by
    cases e : x.1 (Fin.last b)
    · exact (x.2 (walsh_init_last_determine hx e)).elim
    · rfl
  apply Subtype.ext
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [hbit a ha, hbit c hc]
  · exact (congrFun ha j).trans (congrFun hc j).symm

noncomputable def walshEnergy {b : ℕ} (a : NonzeroBinary b) : ℝ :=
  ∫ t in (0:ℝ)..1, (walshCellPrimitive a t)^2

noncomputable def upperWalshEnergy (b : ℕ) : ℝ := 1/12 + 1/(6*((2:ℝ)^b)^2)
noncomputable def lowerWalshEnergy (b : ℕ) : ℝ := 1/48 + 1/(6*((2:ℝ)^b)^2)

theorem walshEnergy_upper {b : ℕ} (a : NonzeroBinary (b+1)) :
    walshEnergy a ≤ upperWalshEnergy (b+1) := by
  rw [walshEnergy, walsh_primitive_energy_exact, upperWalshEnergy]
  have hh : (walshRun (b+1) a.1 : ℝ) ≤ (2:ℝ)^b := by exact_mod_cast walshRun_le_half a.1
  apply add_le_add_left
  have hB : 0<3*((2:ℝ)^(b+1))^2 := by positivity
  apply (div_le_iff₀ hB).mpr
  calc
    _ ≤ ((2:ℝ)^b)^2 := pow_le_pow_left₀ (by positivity) hh 2
    _ = _ := by rw [pow_succ]; ring

theorem walshEnergy_lower_layer {b : ℕ} (a : NonzeroBinary (b+1))
    (h : Fin.init a.1 ≠ fun _ => false) : walshEnergy a ≤ lowerWalshEnergy (b+1) := by
  rw [walshEnergy, walsh_primitive_energy_exact, lowerWalshEnergy]
  have hh' : (walshRun (b+1) a.1 : ℝ)*4 ≤ (2:ℝ)^(b+1) := by
    exact_mod_cast walshRun_lower_layer a.1 h
  have hh : (walshRun (b+1) a.1 : ℝ) ≤ (2:ℝ)^(b+1)/4 := by linarith
  apply add_le_add_left
  have hB : 0<3*((2:ℝ)^(b+1))^2 := by positivity
  apply (div_le_iff₀ hB).mpr
  nlinarith only [pow_le_pow_left₀ (by positivity : 0≤(walshRun (b+1) a.1:ℝ)) hh 2]

theorem walshEnergy_distinct {b : ℕ} (a c : NonzeroBinary (b+1)) (hac : a≠c) :
    (walshEnergy a ≤ lowerWalshEnergy (b+1) ∧ walshEnergy c ≤ upperWalshEnergy (b+1)) ∨
    (walshEnergy a ≤ upperWalshEnergy (b+1) ∧ walshEnergy c ≤ lowerWalshEnergy (b+1)) := by
  by_cases ha : Fin.init a.1 = fun _ => false
  · exact .inr ⟨walshEnergy_upper a, walshEnergy_lower_layer c
      (fun hc => hac (walsh_highest_unique a c ha hc))⟩
  · exact .inl ⟨walshEnergy_lower_layer a ha, walshEnergy_upper c⟩

#print axioms walshEnergy_distinct
end CenteredCubeSqrt
