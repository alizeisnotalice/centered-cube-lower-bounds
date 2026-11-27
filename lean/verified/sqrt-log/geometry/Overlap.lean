import BandCovariance
import LagAssembly

namespace CenteredCube.RudinDensity

open Finset

noncomputable def lagDelta : ℝ := 1/(2-globalMu/2) - 1/2
noncomputable def lagTheta (K : ℕ) (u : ℝ) : ℝ := 8*(1/u^3+1/(K:ℝ))

theorem finite_overlap_budget {K M : ℕ} {a u B S : ℝ}
    (hK : 64 ≤ K) (hu : 1 ≤ u) (ha : 0 < a) (hu₃ : 1 ≤ u^3)
    (hKB : 2*u^2/a^2 ≤ (K:ℝ))
    (hKE : (2*Real.pi*64+8)/(K:ℝ) ≤ min globalMu globalNu/2)
    (t : ℕ → ℝ) (hwind : ∀ i < M, |t i-(K:ℝ)/4| ≤ (K:ℝ)/(100*u))
    (hlag : ∀ i j : ℕ, i < j → j < M → |t i-t j| = ((j-i:ℕ):ℝ)*a/u)
    (F : ℕ × ℕ → ℝ) (hB : 0 ≤ B)
    (hPair : ∀ i j : ℕ, i < j → j < M →
      F (i,j) ≤ B * Real.exp (-(u^2)/(1+kappa K (t i) (t j))))
    (nearBudget : (M:ℝ)*(B * Real.exp (-(u^2)/2))/(Real.exp (a^2)-1) ≤ S/4)
    (midBudget : (M:ℝ)*(32*u/a+1)*
      (B * (Real.exp (-(u^2)/2)*Real.exp (-lagDelta*u^2))) ≤ S/12)
    (outerBudget : (M:ℝ)*(u^3*u/a+1)*
      (B * (Real.exp (-(u^2)/2)*Real.exp (-(1/6)*u^2))) ≤ S/12)
    (farBudget : ((M:ℝ)^2/2)*(B*Real.exp (-(u^2)/(1+lagTheta K u))) ≤ S/12) :
    ∑ p ∈ forwardPairs M, F p ≤ S/2 := by
  have hglobal : ∀ i j : ℕ, i < j → j < M →
      globalNu/2 ≤ 1 + kappa K (t i) (t j) ∧
      (1/8 ≤ |t i-t j| → kappa K (t i) (t j) ≤ 1-globalMu/2) ∧
      (1 ≤ |t i-t j| → |kappa K (t i) (t j)| ≤ 1/(2*|t i-t j|)+8/(K:ℝ)) := by
    intro i j hij hj
    exact covariance_global hK (by linarith) (hwind i (hij.trans hj)) (hwind j hj) hKE
  have hν : 0 < globalNu/2 := div_pos globalNu_pos (by norm_num)
  refine four_region_actual_mass M ha (by linarith) (by positivity) (by positivity)
    (by positivity) (by positivity) F ?_ ?_ ?_ ?_ nearBudget midBudget outerBudget farBudget
  · intro m hm hband i hi
    have hm1 := (mem_Ico.mp hm).1
    have hii : i < i+m := by omega
    have hh : i+m < M := by omega
    have hτ := hlag i (i+m) hii hh
    rw [Nat.add_sub_cancel_left] at hτ
    have hg := hglobal i (i+m) hii hh
    have h0 := band0_covariance (by omega : 4 ≤ K) (by linarith : 3/50 ≤ u)
      ha (hwind i (hii.trans hh)) (hwind (i+m) hh) hm1 hτ hKB hband
    have he := pair_exp_near_lag (by linarith : 0 < u) hτ (hν.trans_le hg.1) h0
    exact (hPair i (i+m) hii hh).trans
      ((mul_le_mul_of_nonneg_left he hB).trans_eq (by ring))
  · intro m hm hband i hi
    have hm1 := (mem_Ico.mp hm).1
    have hii : i < i+m := by omega
    have hh : i+m < M := by omega
    have hτ := hlag i (i+m) hii hh
    rw [Nat.add_sub_cancel_left] at hτ
    have hg := hglobal i (i+m) hii hh
    have hp := reciprocal_cap (hν.trans_le hg.1) (hg.2.1 (band1_lag hτ hband))
    have he : 1/2 + lagDelta ≤ 1/(1+kappa K (t i) (t (i+m))) := by
      unfold lagDelta
      rw [show 1/2+(1/(2-globalMu/2)-1/2) = 1/(2-globalMu/2) by ring,
          show 2-globalMu/2 = 1+(1-globalMu/2) by ring]
      exact hp
    exact (hPair i (i+m) hii hh).trans
      (mul_le_mul_of_nonneg_left (pair_exp_split he) hB)
  · intro m hm hband i hi
    have hm1 := (mem_Ico.mp hm).1
    have hii : i < i+m := by omega
    have hh : i+m < M := by omega
    have hτ := hlag i (i+m) hii hh
    rw [Nat.add_sub_cancel_left] at hτ
    have hg := hglobal i (i+m) hii hh
    have hτ32 := band2_lag hτ hband
    have h0 := covariance_band2 hK hτ32 (hg.2.2 (by linarith))
    have hp := reciprocal_cap (hν.trans_le hg.1) h0
    have he : (1:ℝ)/2+1/6 ≤ 1/(1+kappa K (t i) (t (i+m))) := by
      norm_num at hp ⊢
      exact hp
    exact (hPair i (i+m) hii hh).trans
      (mul_le_mul_of_nonneg_left (pair_exp_split he) hB)
  · rintro ⟨i,j⟩ hp
    have h := mem_filter.mp hp
    have hh := mem_filter.mp h.1
    have hij : i<j := hh.2
    have hj : j<M := mem_range.mp (mem_product.mp hh.1).2
    have hτ := hlag i j hij hj
    have hτ3 := band3_lag hτ h.2
    have hg := hglobal i j hij hj
    have hθ : kappa K (t i) (t j) ≤ lagTheta K u :=
      covariance_band3 (by omega) (by linarith) hτ3 (hg.2.2 (hu₃.trans hτ3))
    have hrec := reciprocal_cap (hν.trans_le hg.1) hθ
    have he : Real.exp (-(u^2)/(1+kappa K (t i) (t j))) ≤
        Real.exp (-(u^2)/(1+lagTheta K u)) := by
      have he' := mul_le_mul_of_nonneg_left hrec (sq_nonneg u)
      apply Real.exp_le_exp.mpr
      simpa only [mul_one_div, neg_div] using neg_le_neg he'
    exact (hPair i j hij hj).trans (mul_le_mul_of_nonneg_left he hB)

end CenteredCube.RudinDensity

#print axioms CenteredCube.RudinDensity.finite_overlap_budget
