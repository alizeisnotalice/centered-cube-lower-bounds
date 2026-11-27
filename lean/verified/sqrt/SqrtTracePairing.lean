import SqrtFiniteField
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

open scoped BigOperators

namespace CenteredCubeSqrt

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- Literal finite-field polynomial for the paper's trace. -/
theorem actual_label_trace_pow {d : ℕ} (hd : 0 < d) (x : LabelField d) :
    algebraMap (ZMod 2) (LabelField d) (Algebra.trace (ZMod 2) (LabelField d) x) =
      ∑ i ∈ Finset.range d, x ^ (2^i) := by
  rw [FiniteField.algebraMap_trace_eq_sum_pow,
    GaloisField.finrank 2 hd.ne', Nat.card_eq_fintype_card, ZMod.card]

/-- The field element indexing a trace character is uniquely determined by
its evaluations. This is the paper's nondegenerate trace pairing. -/
theorem actual_label_trace_injective (d : ℕ) :
    Function.Injective (Algebra.traceForm (ZMod 2) (LabelField d)) := by
  intro x y h
  apply sub_eq_zero.mp
  refine (traceForm_nondegenerate (ZMod 2) (LabelField d)).1 (x-y) ?_
  intro z
  rw [map_sub, h, sub_self]
  rfl

/-- Choose one representative of a fiber; subtraction is a bijection
to the kernel, with inverse given by adding back the representative. -/
def linear_fiber_equiv_ker {R V W : Type*} [Semiring R] [AddCommGroup V] [AddCommGroup W]
    [Module R V] [Module R W] (f : V →ₗ[R] W) (x : V) :
    {v : V // f v = f x} ≃ f.ker where
  toFun y := ⟨y.1-x, by rw [LinearMap.mem_ker, map_sub, y.2, sub_self]⟩
  invFun z := ⟨z.1+x, by rw [map_add, LinearMap.mem_ker.mp z.2, zero_add]⟩
  left_inv y := Subtype.ext (sub_add_cancel _ _)
  right_inv z := Subtype.ext (add_sub_cancel_right _ _)

/-- Exact size of every reachable output fiber of a linear map over F₂. -/
theorem actual_binary_fiber_card {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    [Module (ZMod 2) V] [Module (ZMod 2) W] [Finite V]
    (f : V →ₗ[ZMod 2] W) {y : W} (hy : y ∈ f.range) :
    Nat.card {v : V // f v = y} =
      2^(Module.finrank (ZMod 2) V - Module.finrank (ZMod 2) f.range) := by
  classical
  obtain ⟨x,rfl⟩ := hy
  let : Fintype V := Fintype.ofFinite V
  let : Fintype f.ker := Fintype.ofFinite f.ker
  have rk := f.finrank_range_add_finrank_ker
  rw [Nat.card_congr (linear_fiber_equiv_ker f x), Nat.card_eq_fintype_card,
    Module.card_fintype (Module.finBasis (ZMod 2) f.ker), ZMod.card, Fintype.card_fin]
  congr 1
  omega

#print axioms actual_label_trace_pow
#print axioms actual_label_trace_injective
#print axioms actual_binary_fiber_card

end CenteredCubeSqrt
