import SqrtTraceRank
import SqrtTraceNonzeroFiber

namespace CenteredCubeSqrt

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
open Classical

abbrev LabelOutput (b : ℕ) := (Fin b ⊕ Fin b) → ZMod 2

noncomputable def jointTraceRows {b d : ℕ} (t : Fin b → LabelField d) (g : (LabelField d)ˣ) :
    Fin b ⊕ Fin b → LabelField d :=
  Sum.elim t (fun i => (g:LabelField d)*t i)

noncomputable def jointTrace {b d : ℕ} (t : Fin b → LabelField d) (g : (LabelField d)ˣ) :
    LabelField d →ₗ[ZMod 2] LabelOutput b := traceLabelMap (jointTraceRows t g)

noncomputable def traceOverlap {b d : ℕ} (t : Fin b → LabelField d) (g : (LabelField d)ˣ) :
    Submodule (ZMod 2) (LabelField d) :=
  Submodule.span (ZMod 2) (Set.range t) ⊓
    Submodule.span (ZMod 2) (Set.range fun i => (g:LabelField d)*t i)

/-- The joint trace labels have rank (2b-dim(Wcap gW)). -/
theorem jointTrace_rank {b d : ℕ} {t : Fin b → LabelField d}
    (ht : LinearIndependent (ZMod 2) t) (g : (LabelField d)ˣ) :
    Module.finrank (ZMod 2) (jointTrace t g).range =
      2*b - Module.finrank (ZMod 2) (traceOverlap t g) := by
  let W : Submodule (ZMod 2) (LabelField d) := Submodule.span (ZMod 2) (Set.range t)
  let Wg : Submodule (ZMod 2) (LabelField d) := Submodule.span (ZMod 2) (Set.range fun i => (g:LabelField d)*t i)
  have hmul : Function.Injective (LinearMap.mulLeft (ZMod 2) (g:LabelField d)) :=
    fun _ _ h => mul_left_cancel₀ (Units.ne_zero g) h
  have hg : LinearIndependent (ZMod 2) (fun i => (g:LabelField d)*t i) :=
    ht.map' (LinearMap.mulLeft (ZMod 2) (g:LabelField d)) (LinearMap.ker_eq_bot.mpr hmul)
  have hW : Module.finrank (ZMod 2) W = b := by
    simpa [W] using finrank_span_eq_card ht
  have hWg : Module.finrank (ZMod 2) Wg = b := by
    simpa [Wg] using finrank_span_eq_card hg
  have hr := Submodule.finrank_sup_add_finrank_inf_eq W Wg
  rw [hW,hWg] at hr
  unfold jointTrace
  rw [actual_traceLabel_rank, jointTraceRows, Set.Sum.elim_range, Submodule.span_union]
  change Module.finrank (ZMod 2) ↥(W ⊔ Wg) = 2*b - Module.finrank (ZMod 2) ↥(W ⊓ Wg)
  omega

theorem jointTrace_nonzero_fiber {b d : ℕ} {t : Fin b → LabelField d}
    (hd : 0 < d) (ht : LinearIndependent (ZMod 2) t) (g : (LabelField d)ˣ)
    {y : LabelOutput b} (hy : y ∈ (jointTrace t g).range) :
    Nat.card {x : LabelField d // jointTrace t g x = y ∧ x ≠ 0} =
      2^(d-(2*b-Module.finrank (ZMod 2) (traceOverlap t g))) - if y=0 then 1 else 0 := by
  rw [finite_linear_nonzero_fiber, actual_binary_fiber_card _ hy,
    jointTrace_rank ht g, GaloisField.finrank 2 hd.ne']
  by_cases hy0 : y=0 <;> simp [hy0]

theorem jointTrace_regular_fiber {b d : ℕ} {t : Fin b → LabelField d}
    (hd : 0 < d) (ht : LinearIndependent (ZMod 2) t) (g : (LabelField d)ˣ)
    (hr : traceOverlap t g = ⊥) (y : LabelOutput b) :
    Nat.card {x : LabelField d // jointTrace t g x = y ∧ x ≠ 0} =
      2^(d-2*b) - if y=0 then 1 else 0 := by
  have rwk : Module.finrank (ZMod 2) (jointTrace t g).range = 2*b := by
    rw [jointTrace_rank ht, hr, finrank_bot, Nat.sub_zero]
  have hrange : (jointTrace t g).range = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [rwk]
    simp [LabelOutput, two_mul]
  have hy : y ∈ (jointTrace t g).range := by rw [hrange]; trivial
  rw [jointTrace_nonzero_fiber hd ht g hy, hr, finrank_bot, Nat.sub_zero]

#print axioms jointTrace_rank
#print axioms jointTrace_nonzero_fiber
#print axioms jointTrace_regular_fiber

end CenteredCubeSqrt
