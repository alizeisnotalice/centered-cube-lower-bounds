import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Tactic

open scoped Topology

namespace CubeSqrtProbability

/-- The k-th coefficient of the scalar path derivative is evaluation of the
k-linear Fréchet derivative on the repeated increment. In particular, orders
one and two are linear and quadratic contractions of that increment. -/
theorem iteratedDeriv_line_eq_iteratedFDeriv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (k : ℕ) (hf : ContDiff ℝ k f) (z d : E) :
    iteratedDeriv k (fun t : ℝ ↦ f (z+t • d)) 0 =
      iteratedFDeriv ℝ k f z (fun _ : Fin k ↦ d) := by
  let L : ℝ →L[ℝ] E := (ContinuousLinearMap.id ℝ ℝ).smulRight d
  let g : E → ℝ := fun x ↦ f (z+x)
  have hg : ContDiff ℝ k g := hf.comp (contDiff_const.add contDiff_id)
  have hL (t : ℝ) : L t = t • d := rfl
  have heq : (fun t : ℝ ↦ f (z+t • d)) = g ∘ L := by ext t; rfl
  rw [heq,iteratedDeriv_eq_iteratedFDeriv,L.iteratedFDeriv_comp_right hg 0 (by simp)]
  have h : iteratedFDeriv ℝ k g 0 = iteratedFDeriv ℝ k f z := by
    unfold g
    rw [iteratedFDeriv_comp_add_left,add_zero]
  rw [L.map_zero,h]
  simp [hL]

end CubeSqrtProbability
#print axioms CubeSqrtProbability.iteratedDeriv_line_eq_iteratedFDeriv
