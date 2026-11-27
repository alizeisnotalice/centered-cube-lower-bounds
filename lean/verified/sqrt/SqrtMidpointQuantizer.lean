import SqrtWindowPulse
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace CenteredCubeSqrt
open MeasureTheory Set
open scoped Interval BigOperators

noncomputable def midpointError (B : ℕ) (r : ℝ) : ℝ :=
  (((Finset.range B).filter (fun y : ℕ => ((y:ℝ)+1/2)/(B:ℝ)≤r)).card:ℝ)/B-r

theorem midpointError_in_cell {B j : ℕ} (hj : j<B) {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    midpointError B (((j:ℝ)+t)/(B:ℝ)) =
      if t<1/2 then (-t)/(B:ℝ) else (1-t)/(B:ℝ) := by
  classical
  have hB : 0<(B:ℝ) := by exact_mod_cast (show 0<B by omega)
  have hfilter : (Finset.range B).filter
      (fun y : ℕ => ((y:ℝ)+1/2)/(B:ℝ)≤((j:ℝ)+t)/(B:ℝ)) =
      Finset.range (if t<1/2 then j else j+1) := by
    ext y
    simp only [Finset.mem_filter,Finset.mem_range,div_le_div_iff_of_pos_right hB]
    by_cases ht2 : t<1/2
    · rw [ite_eq_left ht2]
      constructor
      · intro h
        by_contra! hh
        have h' : (j:ℝ)≤y := by exact_mod_cast hh
        linarith [h.2]
      · intro h
        refine ⟨h.trans hj,?_⟩
        have h' : (y:ℝ)+1≤j := by exact_mod_cast (show y+1≤j by omega)
        linarith [ht.1]
    · rw [ite_eq_right ht2]
      constructor
      · intro h
        by_contra! hh
        have h' : (j:ℝ)+1≤y := by exact_mod_cast hh
        linarith [h.2,ht.2]
      · intro h
        refine ⟨by omega,?_⟩
        have h' : (y:ℝ)≤j := by exact_mod_cast (show y≤j by omega)
        linarith
  unfold midpointError
  rw [hfilter,Finset.card_range]
  split <;> push_cast <;> ring

theorem midpointError_abs_in_cell {B j : ℕ} (hj : j<B) {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    |midpointError B (((j:ℝ)+t)/(B:ℝ))|≤1/(2*(B:ℝ)) := by
  have hB : 0<(B:ℝ) := by exact_mod_cast (show 0<B by omega)
  rw [midpointError_in_cell hj ht]
  split
  · rename_i h
    rw [abs_div,abs_of_pos hB,abs_neg,abs_of_nonneg ht.1]
    have e : 1/(2*(B:ℝ))=(1/2)/(B:ℝ) := by ring
    rw [e]
    exact div_le_div_of_nonneg_right h.le hB.le
  · rename_i h
    rw [abs_div,abs_of_pos hB,abs_of_nonneg (by linarith [ht.2])]
    have e : 1/(2*(B:ℝ))=(1/2)/(B:ℝ) := by ring
    rw [e]
    apply div_le_div_of_nonneg_right _ hB.le
    linarith

#print axioms midpointError_in_cell
#print axioms midpointError_abs_in_cell

end CenteredCubeSqrt
