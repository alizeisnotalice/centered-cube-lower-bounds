import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Tactic

open Filter Set
open scoped Topology

namespace CubeSqrtProbability

/-- All positive-order derivatives of the transition are supported on its
unit-width transition interval and hence have a global finite bound. -/
theorem exists_bound_iteratedDeriv_smoothTransition (m : ℕ) (hm : 0 < m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, |iteratedDeriv m Real.smoothTransition x| ≤ C := by
  have hd : Continuous (iteratedDeriv m Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := m)).continuous_iteratedDeriv' m
  obtain ⟨C,hC⟩ := (isCompact_Icc (a := (0:ℝ)) (b := 1)).bddAbove_image hd.abs.continuousOn
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro x
  by_cases hx : x ∈ Icc (0:ℝ) 1
  · exact (hC (mem_image_of_mem _ hx)).trans (le_max_left _ _)
  · have hz : iteratedDeriv m Real.smoothTransition x = 0 := by
      by_cases hx0 : x < 0
      · have he : Real.smoothTransition =ᶠ[𝓝 x] (fun _ ↦ (0:ℝ)) := by
          filter_upwards [Iio_mem_nhds hx0] with y hy
          exact Real.smoothTransition.zero_of_nonpos hy.le
        rw [he.iteratedDeriv_eq m, iteratedDeriv_const]
        simp [hm.ne']
      · have hx1 : 1 < x := lt_of_not_ge (fun h ↦ hx ⟨le_of_not_gt hx0,h⟩)
        have he : Real.smoothTransition =ᶠ[𝓝 x] (fun _ ↦ (1:ℝ)) := by
          filter_upwards [Ioi_mem_nhds hx1] with y hy
          exact Real.smoothTransition.one_of_one_le hy.le
        rw [he.iteratedDeriv_eq m, iteratedDeriv_const]
        simp [hm.ne']
    simp [hz]

end CubeSqrtProbability
#print axioms CubeSqrtProbability.exists_bound_iteratedDeriv_smoothTransition
