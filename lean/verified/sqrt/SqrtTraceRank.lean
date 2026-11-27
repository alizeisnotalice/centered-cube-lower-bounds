import SqrtTracePairing
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Dual.Basis

namespace CenteredCubeSqrt

open scoped BigOperators Matrix

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

noncomputable def traceLabelMap {ι : Type*} {d : ℕ} (rows : ι → LabelField d) :
    LabelField d →ₗ[ZMod 2] (ι → ZMod 2) :=
  LinearMap.pi fun i => Algebra.traceForm (ZMod 2) (LabelField d) (rows i)

@[simp] theorem traceLabelMap_apply {ι : Type*} {d : ℕ}
    (rows : ι → LabelField d) (x : LabelField d) (i : ι) :
    traceLabelMap rows x i = Algebra.trace (ZMod 2) (LabelField d) (rows i*x) := rfl

/-- Ranks of all actual trace-label systems are ranks of their field row
spans, including the singular/defective case. -/
theorem actual_traceLabel_rank {ι : Type*} [Finite ι] {d : ℕ} (rows : ι → LabelField d) :
    Module.finrank (ZMod 2) (traceLabelMap rows).range =
      Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range rows)) := by
  classical
  let E := LabelField d
  let R := ZMod 2
  let k := Module.finrank R E
  let basis : Module.Basis (Fin k) R E := Module.finBasis R E
  let coord : E →ₗ[R] (Fin k → R) :=
    basis.dualBasis.equivFun.toLinearMap.comp (Algebra.traceForm R E)
  have hcoord : Function.Injective coord :=
    basis.dualBasis.equivFun.injective.comp (actual_label_trace_injective d)
  let A : Matrix ι (Fin k) R := fun i j => coord (rows i) j
  have hcalc : A.mulVecLin.comp basis.equivFun.toLinearMap = traceLabelMap rows := by
    ext x i
    simp only [LinearMap.comp_apply, Matrix.mulVecLin_apply, Matrix.mulVec_apply_eq_sum]
    change _ = Algebra.traceForm R E (rows i) x
    have e := congrArg (fun y => Algebra.traceForm R E (rows i) y) (basis.sum_repr x)
    rw [map_sum] at e
    simpa [A, coord, Module.Basis.dualBasis_equivFun, Module.Basis.equivFun_apply, mul_comm] using e
  have hRange : A.mulVecLin.range = (traceLabelMap rows).range := by
    rw [← hcalc]
    ext y
    constructor
    · rintro ⟨v,rfl⟩
      obtain ⟨x,hx⟩ := basis.equivFun.surjective v
      exact ⟨x, by simp [hx]⟩
    · rintro ⟨x,rfl⟩
      exact ⟨basis.equivFun x, rfl⟩
  have rowSpan :
      Submodule.span R (Set.range A.row) = (Submodule.span R (Set.range rows)).map coord := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  rw [← hRange]
  change A.rank = _
  rw [Matrix.rank_eq_finrank_span_row, rowSpan]
  exact (Submodule.equivMapOfInjective coord hcoord
    (Submodule.span R (Set.range rows))).finrank_eq.symm

#print axioms actual_traceLabel_rank

end CenteredCubeSqrt
