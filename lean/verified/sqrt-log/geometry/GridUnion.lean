import ActualSingles
import HaloUnion
import Overlap

namespace CenteredCube.RudinDensity

open Finset MeasureTheory Set

noncomputable def pairPrefactor (u : ℝ) : ℝ := (Real.exp 1 * CubeMD.mdUpperConstant)/u

theorem grid_union_lower {n K M : ℕ} {a u p : ℝ} (hn : 0 < n)
    (hK : 64 ≤ K) (hu : 1 ≤ u) (ha : 0 < a)
    (hKB : 2*u^2/a^2 ≤ (K:ℝ))
    (hKE : (2*Real.pi*64+8)/(K:ℝ) ≤ min globalMu globalNu/2)
    (t : ℕ → ℝ) (hwind : ∀ i < M, |t i-(K:ℝ)/4| ≤ (K:ℝ)/(100*u))
    (hlag : ∀ i j : ℕ, i < j → j < M → |t i-t j| = ((j-i:ℕ):ℝ)*a/u)
    (E : ℕ → Set (Fin n → ℝ)) (hE : ∀ i, MeasurableSet (E i))
    (hsub : ∀ i < M, E i ⊆ {v | u ≤ normalizedRow (normalizedScore K (t i)) v})
    (hM : ∀ i < M, p ≤ (cellLaw n).real (E i))
    (hN : readyMD n (pairB (globalNu/2)))
    (hWin : (2*u/Real.sqrt (2*(globalNu/2)))^6 ≤ (n:ℝ))
    (hErr : 72*(pairB (globalNu/2))^3*(2*u/Real.sqrt (2*(globalNu/2)))^3/
      Real.sqrt (n:ℝ) ≤ 1)
    (nearBudget : (M:ℝ)*(pairPrefactor u * Real.exp (-(u^2)/2))/
      (Real.exp (a^2)-1) ≤ ((M:ℝ)*p)/4)
    (midBudget : (M:ℝ)*(32*u/a+1)*
      (pairPrefactor u * (Real.exp (-(u^2)/2)*Real.exp (-lagDelta*u^2))) ≤ ((M:ℝ)*p)/12)
    (outerBudget : (M:ℝ)*(u^3*u/a+1)*
      (pairPrefactor u * (Real.exp (-(u^2)/2)*Real.exp (-(1/6)*u^2))) ≤ ((M:ℝ)*p)/12)
    (farBudget : ((M:ℝ)^2/2)*(pairPrefactor u*Real.exp (-(u^2)/(1+lagTheta K u))) ≤
      ((M:ℝ)*p)/12) :
    (M:ℝ)*p/2 ≤ (cellLaw n).real (⋃ j < M, E j) := by
  have hu0 : 0 < u := by linarith
  have hu₃ : 1 ≤ u^3 := by
    simpa using pow_le_pow_left₀ (by norm_num : 0 ≤ (1:ℝ)) hu 3
  have hB : 0 ≤ pairPrefactor u := by
    unfold pairPrefactor
    exact div_nonneg (mul_nonneg (Real.exp_pos _).le mdUpper_nonneg) hu0.le
  have hpoint : ∀ i j : ℕ, i<j → j<M →
      (cellLaw n).real (E i ∩ E j) ≤
        pairPrefactor u * Real.exp (-(u^2)/(1+kappa K (t i) (t j))) := by
    intro i j hij hj
    have hi := hij.trans hj
    have H := covariance_global hK (by linarith : (4:ℝ)/25 ≤ u) (hwind i hi) (hwind j hj) hKE
    have hε : 0 < globalNu/2 := div_pos globalNu_pos (by norm_num)
    exact (measureReal_mono (Set.inter_subset_inter (hsub i hi) (hsub j hj))).trans
      (two_point_actual_bound (by omega) hn hu hε H.1
        (hwind i hi) (hwind j hj) hN hWin hErr)
  have hS : (M:ℝ)*p ≤ ∑ j ∈ Finset.range M, (cellLaw n).real (E j) := by
    simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using
      (Finset.sum_le_sum (fun j hj => hM j (Finset.mem_range.mp hj)) :
        (∑ _j ∈ Finset.range M, p) ≤ ∑ j ∈ Finset.range M, (cellLaw n).real (E j))
  have ho := finite_overlap_budget hK hu ha hu₃ hKB hKE t hwind hlag
    (fun p => (cellLaw n).real (E p.1 ∩ E p.2)) hB hpoint
    nearBudget midBudget outerBudget farBudget
  apply half_marginal_halo_mass (cellLaw n) E hE M p hM
  exact ho.trans (div_le_div_of_nonneg_right hS (by norm_num))

end CenteredCube.RudinDensity

#print axioms CenteredCube.RudinDensity.grid_union_lower
