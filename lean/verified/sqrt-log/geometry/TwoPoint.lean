import KernelMoments
import GlobalKernel

open Finset

namespace CenteredCube.RudinDensity

theorem sumScore_abs_le {K : ℕ} (hK : 4 ≤ K) {u t s ε : ℝ}
    (hu : 3/50 ≤ u) (hε : 0 < ε) (hκ : ε ≤ 1 + kappa K t s)
    (ht : |t - (K:ℝ)/4| ≤ (K:ℝ)/(100*u))
    (hs : |s - (K:ℝ)/4| ≤ (K:ℝ)/(100*u)) (x : ℝ) :
    |sumScore K t s x| ≤ (2*(5 * Real.sqrt 8)) / Real.sqrt (2*ε) := by
  have h1 := normalizedScore_abs_le hK hu ht x
  have h2 := normalizedScore_abs_le hK hu hs x
  have h0 : 0 < Real.sqrt (2*ε) := Real.sqrt_pos.2 (by positivity)
  have hd : Real.sqrt (2*ε) ≤ Real.sqrt (2*(1 + kappa K t s)) :=
    Real.sqrt_le_sqrt (by linarith)
  unfold sumScore
  rw [abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact (div_le_div_of_nonneg_right ((abs_add_le _ _).trans (by linarith)) (h0.le.trans hd)).trans
    (div_le_div_of_nonneg_left (by positivity) h0 hd)

noncomputable def normalizedRow {n : ℕ} (X : ℝ → ℝ) (v : Fin n → ℝ) : ℝ :=
  (∑ i, X (v i)) / Real.sqrt n

noncomputable def pairThreshold (K : ℕ) (t s u : ℝ) : ℝ :=
  2*u / Real.sqrt (2*(1 + kappa K t s))

theorem two_point_subset {K n : ℕ} (hn : 0 < n)
    {t s u : ℝ} (hκ : 0 < 1 + kappa K t s) :
    ({v : Fin n → ℝ | u ≤ normalizedRow (normalizedScore K t) v} ∩
      {v | u ≤ normalizedRow (normalizedScore K s) v}) ⊆
      {v | pairThreshold K t s u ≤ normalizedRow (sumScore K t s) v} := by
  intro v hv
  have ht : u ≤ normalizedRow (normalizedScore K t) v := hv.1
  have hs : u ≤ normalizedRow (normalizedScore K s) v := hv.2
  change pairThreshold K t s u ≤ normalizedRow (sumScore K t s) v
  have hden : 0 < Real.sqrt (2*(1 + kappa K t s)) := Real.sqrt_pos.2 (by positivity)
  have he : normalizedRow (sumScore K t s) v =
      (normalizedRow (normalizedScore K t) v + normalizedRow (normalizedScore K s) v) /
        Real.sqrt (2*(1 + kappa K t s)) := by
    unfold normalizedRow sumScore
    rw [← Finset.sum_div, Finset.sum_add_distrib, ← add_div]
    ring
  rw [he]
  unfold pairThreshold
  exact div_le_div_of_nonneg_right (by linarith) hden.le

theorem pairThreshold_exponent {K : ℕ} {t s u : ℝ} (hκ : 0 < 1 + kappa K t s) :
    pairThreshold K t s u ^ 2 / 2 = u^2 / (1 + kappa K t s) := by
  unfold pairThreshold
  rw [div_pow, Real.sq_sqrt (by positivity)]
  have hn : 1 + kappa K t s ≠ 0 := hκ.ne'
  field_simp
  <;> ring

end CenteredCube.RudinDensity

#print axioms CenteredCube.RudinDensity.sumScore_abs_le
#print axioms CenteredCube.RudinDensity.two_point_subset
#print axioms CenteredCube.RudinDensity.pairThreshold_exponent
