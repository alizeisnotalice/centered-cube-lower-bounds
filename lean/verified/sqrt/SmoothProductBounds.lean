import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic

open scoped BigOperators

namespace CubeSqrtProbability

/-- The coarse constant `(8*C)^J` is independent of all face heights.
The important part for a fixed number of faces is the homogeneous factor
`Q^m` for the m-th directional derivative, up to order three. -/
theorem smooth_finite_product_iteratedDeriv_bound {ι : Type*} (s : Finset ι)
    (f : ι → ℝ → ℝ) (C Q : ℝ) (hC : 1 ≤ C) (hQ : 0 ≤ Q)
    (hf : ∀ i ∈ s, ContDiff ℝ 3 (f i))
    (h : ∀ i ∈ s, ∀ m : ℕ, m ≤ 3 → ∀ z : ℝ,
        |iteratedDeriv m (f i) z| ≤ C*Q^m) :
    ∀ m : ℕ, m ≤ 3 → ∀ z : ℝ,
      |iteratedDeriv m (fun y : ℝ ↦ ∏ i ∈ s, f i y) z| ≤ (8*C)^s.card*Q^m := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro m hm z
    cases m with
    | zero => simp
    | succ m => simp [iteratedDeriv_const, pow_nonneg hQ]
  | insert a s ha ih =>
    intro m hm z
    let g := fun x : ℝ ↦ ∏ i ∈ s, f i x
    have hg : ContDiff ℝ 3 g := by
      unfold g
      have hf' (i : ι) (hi : i ∈ s) : ContDiff ℝ 3 (f i) :=
        hf i (Finset.mem_insert_of_mem hi)
      have hp (T : Finset ι) (hT : ∀ j ∈ T, ContDiff ℝ 3 (f j)) :
          ContDiff ℝ 3 (fun x : ℝ ↦ ∏ j ∈ T, f j x) := by
        induction T using Finset.induction_on with
        | empty => simpa using (contDiff_const : ContDiff ℝ 3 (fun _ : ℝ ↦ (1:ℝ)))
        | insert i T hi ih' =>
          simp only [Finset.prod_insert hi]
          exact (hT i (Finset.mem_insert_self i T)).mul
            (ih' (fun j hj ↦ hT j (Finset.mem_insert_of_mem hj)))
      exact hp s hf'
    have hC0 : 0 ≤ C := by linarith
    have hD0 : 0 ≤ (8*C)^s.card := pow_nonneg (by positivity) _
    have h2 : (2:ℝ)^m ≤ 8 := by
      interval_cases m <;> norm_num
    have heq : (fun y : ℝ ↦ ∏ i ∈ insert a s, f i y) = fun y ↦ f a y * g y := by
      funext y
      simp [g,Finset.prod_insert ha]
    have hfa : ContDiff ℝ m (f a) := (hf a (Finset.mem_insert_self a s)).of_le (by exact_mod_cast hm)
    have hg' : ContDiff ℝ m g := hg.of_le (by exact_mod_cast hm)
    rw [heq, iteratedDeriv_fun_mul hfa.contDiffAt hg'.contDiffAt]
    set B : ℝ := (8*C)^s.card
    calc
      _ ≤ ∑ j ∈ Finset.range (m+1), |(m.choose j:ℝ) *
          iteratedDeriv j (f a) z * iteratedDeriv (m-j) g z| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ Finset.range (m+1), (m.choose j:ℝ) * (C*B*Q^m) := by
        refine Finset.sum_le_sum (fun j hj ↦ ?_)
        have hjm : j ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
        have hj' := h a (Finset.mem_insert_self a s) j (hjm.trans hm) z
        have hrest := ih (fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))
            (fun i hi ↦ h i (Finset.mem_insert_of_mem hi))
            (m-j) ((Nat.sub_le _ _).trans hm) z
        have hab : Q^j * Q^(m-j) = Q^m := by rw [← pow_add, Nat.add_sub_of_le hjm]
        have hc : 0 ≤ (m.choose j:ℝ) := by positivity
        rw [abs_mul,abs_mul,abs_of_nonneg hc]
        calc
          _ ≤ (m.choose j:ℝ) * (C*Q^j) * (B*Q^(m-j)) := by
            gcongr
          _ = _ := by
            rw [show (m.choose j:ℝ) * (C*Q^j) * (B*Q^(m-j)) =
                (m.choose j:ℝ)*(C*B*(Q^j * Q^(m-j))) by ring, hab]
      _ = (2:ℝ)^m * (C*B*Q^m) := by
        rw [← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose, Nat.cast_pow]
        norm_num
      _ ≤ 8 * (C*B*Q^m) := mul_le_mul_of_nonneg_right h2 (by positivity)
      _ = (8*C)^(insert a s).card*Q^m := by
        rw [Finset.card_insert_of_notMem ha,pow_succ]
        dsimp [B]
        ring

end CubeSqrtProbability
#print axioms CubeSqrtProbability.smooth_finite_product_iteratedDeriv_bound
