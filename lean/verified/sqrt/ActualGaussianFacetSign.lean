import GaussianFacetNull
import ActualFaceMoments

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ProbabilityTheory
namespace CubeSqrtProbability

theorem true_winner_gaussian_facet_sign {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) {k : ℕ} (j : Fin k)
    (G : Ω → Fin k → ℝ) (hG : Measurable G) (n : ℕ) :
    let F (w : Ω) := winnerFacetScore j (G w)
    let m i := ∫ w, F w i ∂Q
    let μ := Q.map (fun w i ↦ F w i-m i)
    let S := rawSecondMoment μ
    let z (i : WinnerFacet j) := n*m i
    S.PosSemidef →
    ∀ᵐ x ∂sumLaw (centeredGaussianCompanion S) n,
      (z+x) (.inl false) = -(z+x) (.inl true) := by
  classical
  dsimp only
  intro hS
  let F (w : Ω) := winnerFacetScore j (G w)
  have hmF : Measurable F := (measurable_winnerFacetScore j).comp hG
  let m i := ∫ w, F w i ∂Q
  let μ := Q.map (fun w i ↦ F w i-m i)
  let S := rawSecondMoment μ
  let l : WinnerFacet j := .inl false
  let u : WinnerFacet j := .inl true
  have hlu : (fun w ↦ F w l) = (fun w ↦ -F w u) := rfl
  have hn : S l l + S l u + S u l + S u u=0 := by
    change rawSecondMoment μ l l + rawSecondMoment μ l u + rawSecondMoment μ u l +
      rawSecondMoment μ u u = 0
    simp only [μ, m, centered_facet_raw_matrix_covariance Q F hmF, hlu,
      covariance_fun_neg_left, covariance_fun_neg_right]
    ring
  have hmean : m l = -m u := by
    change (∫ w, F w l ∂Q) = -(∫ w, F w u ∂Q)
    rw [hlu,integral_neg]
  have hs := gaussian_companion_sum_ae_opposite S hS l u n hn
  filter_upwards [hs] with x hx
  change (n:ℝ)*m l + x l = -((n:ℝ)*m u+x u)
  rw [hmean,hx]
  ring

end CubeSqrtProbability
#print axioms CubeSqrtProbability.true_winner_gaussian_facet_sign
