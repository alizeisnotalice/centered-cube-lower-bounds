import ActualSingles
import GoodEvent
import PointThreshold

open MeasureTheory ProbabilityTheory Set
namespace CenteredCube.RudinDensity

noncomputable def centerScale (n K : ℕ) : ℝ :=
  Real.sqrt (n:ℝ) / (90*Real.pi*(K:ℝ))

noncomputable def pointScale (n K : ℕ) (t : ℝ) : ℝ :=
  Real.sqrt (n:ℝ) * sigma K t

noncomputable def pointThreshold (n K : ℕ) (t : ℝ) : ℝ :=
  CubeMD.singleThreshold (centerScale n K) (pointScale n K t)

noncomputable def goodPoint (n K : ℕ) (t : ℝ) : Set (Fin n → ℝ) :=
  CubeMD.quadraticGood (normalizedScore K t) (sigma K t) (pointScale n K t)

noncomputable def hitPoint (n K : ℕ) (t : ℝ) : Set (Fin n → ℝ) :=
  {v | pointThreshold n K t ≤ normalizedRow (normalizedScore K t) v} ∩ goodPoint n K t

theorem physical_threshold_stable {n K : ℕ} (hK : 4 ≤ K) {t : ℝ}
    (hu : 1 ≤ centerScale n K) (hKu : 32*centerScale n K ≤ (K:ℝ))
    (ht : |t-(K:ℝ)/4| ≤ (K:ℝ)/(100*centerScale n K)) :
    0 < pointScale n K t ∧ centerScale n K ≤ pointThreshold n K t ∧
      pointThreshold n K t ≤ 2*centerScale n K ∧
      pointThreshold n K t ^ 2 - centerScale n K ^ 2 ≤ 1 ∧
      pointScale n K t ≤ 2*centerScale n K := by
  let u := centerScale n K
  let v := pointScale n K t
  let ρ := rfun K t / (3/2)
  let V := 4*VK K t/(K:ℝ)
  have hK' : 0 < (K:ℝ) := by exact_mod_cast (by omega : 0 < K)
  have hu' : 0 < u := by linarith
  have hu75 : 3/50 ≤ u := by linarith
  have hV : |V-1| ≤ 2/(K:ℝ) := by
    have he : V-1 = 4/(K:ℝ)*(VK K t-(K:ℝ)/4) := by dsimp only [V]; field_simp [hK'.ne'] <;> ring
    rw [he,abs_mul,abs_of_nonneg (by positivity : (0:ℝ) ≤ 4/(K:ℝ))]
    have hh := mul_le_mul_of_nonneg_left (VK_window hK hu75 ht).1
      (by positivity : (0:ℝ) ≤ 4/(K:ℝ))
    exact hh.trans_eq (by ring)
  have hρ : |ρ-1| ≤ 1/(75*u) := by
    have he : ρ-1 = (4/(3*(K:ℝ)))*(t-(K:ℝ)/4) := by
      dsimp only [ρ]; unfold rfun; field_simp [hK'.ne'] <;> ring
    rw [he,abs_mul,abs_of_nonneg (by positivity : (0:ℝ) ≤ 4/(3*(K:ℝ)))]
    have hh := mul_le_mul_of_nonneg_left ht (by positivity : (0:ℝ) ≤ 4/(3*(K:ℝ)))
    exact hh.trans_eq (by field_simp [hK'.ne',hu'.ne']; ring)
  have hr : 0 < rfun K t := by
    have h' : 1/(75*u) ≤ (1:ℝ)/75 := by
      apply (div_le_iff₀ (by positivity : 0 < 75*u)).mpr
      linarith
    have hh := (abs_le.mp (hρ.trans h')).1
    dsimp only [ρ] at hh
    linarith
  have hVr : 0 < VK K t := (by positivity : (0:ℝ) < (K:ℝ)/8).trans_le
    (VK_window hK hu75 ht).2.1
  have hV0 : 0 ≤ V := by dsimp only [V]; positivity
  have hρ0 : 0 < ρ := by dsimp only [ρ]; positivity
  have hσ0 : 0 ≤ sigmaSq K t := by unfold sigmaSq; positivity
  have hsig : sigma K t = (1/(90*Real.pi*(K:ℝ))) * (Real.sqrt V / ρ) := by
    have he : (sigma K t)^2 = ((1/(90*Real.pi*(K:ℝ))) * (Real.sqrt V / ρ))^2 := by
      unfold sigma
      rw [Real.sq_sqrt hσ0, mul_pow, div_pow (Real.sqrt V) ρ, Real.sq_sqrt hV0]
      dsimp only [V,ρ]
      unfold sigmaSq
      field_simp [hK'.ne', Real.pi_ne_zero, hr.ne'] <;> ring
    have hnσ : 0 ≤ sigma K t := Real.sqrt_nonneg _
    have hnOther : 0 ≤ (1/(90*Real.pi*(K:ℝ))) * (Real.sqrt V / ρ) := by positivity
    exact le_antisymm (le_of_sq_le_sq he.le hnOther) (le_of_sq_le_sq he.ge hnσ)
  have hv : v = u*(Real.sqrt V/ρ) := by
    dsimp only [v,pointScale,u,centerScale]
    rw [hsig]; ring
  have habs : |v-u| ≤ 1/8 := by
    rw [hv]
    exact CubeMD.scale_displacement_of_ratios u (K:ℝ) ρ V hu hKu hρ hV
  obtain ⟨hv' ,hzu,hzul,hzs⟩ := CubeMD.singleThreshold_stable u v hu habs
  exact ⟨hv',hzu,hzul,hzs,by linarith [(abs_le.mp habs).2]⟩

theorem point_quadratic_good_bad {n K : ℕ} (hK : 4 ≤ K) (hn : 0 < n) {t : ℝ}
    (hu : 1 ≤ centerScale n K) (hKu : 32*centerScale n K ≤ (K:ℝ))
    (ht : |t-(K:ℝ)/4| ≤ (K:ℝ)/(100*centerScale n K)) :
    (cellLaw n).real (goodPoint n K t)ᶜ ≤
      Real.exp (-((n:ℝ)/(32*(scoreB^2+1)^2*centerScale n K^4))) := by
  have hp := physical_threshold_stable hK hu hKu ht
  have hu75 : 3/50 ≤ centerScale n K := by linarith only [hu]
  have hK' : 0 < (K:ℝ) := by exact_mod_cast (by omega : 0 < K)
  have hV : 0 < VK K t := (by positivity : (0:ℝ) < (K:ℝ)/8).trans_le (VK_window hK hu75 ht).2.1
  have hσ : (sigma K t)^2 = (pointScale n K t)^2/(n:ℝ) := by
    have hn' : 0 < (n:ℝ) := by exact_mod_cast hn
    unfold pointScale
    rw [mul_pow, Real.sq_sqrt hn'.le]
    field_simp [hn'.ne']
  have hB : 0 ≤ scoreB := by unfold scoreB; positivity
  have hh := CubeMD.quadraticGood_bad_probability (μ := unitLaw) hn (normalizedScore K t)
    (normalizedScore_cont K t).measurable scoreB hB
    (Filter.Eventually.of_forall (by simpa only [scoreB] using normalizedScore_abs_le hK hu75 ht))
    (score_law_var K (by omega) t hV) (sigma K t) (pointScale n K t) hp.1 hσ
  apply hh.trans
  apply Real.exp_le_exp.mpr
  apply neg_le_neg
  have hu0 : 0 < centerScale n K := by linarith only [hu]
  have hv0 : 0 < pointScale n K t := hp.1
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  have hp4 := pow_le_pow_left₀ hp.1.le hp.2.2.2.2 (4:ℕ)
  calc
    _ ≤ 2*(scoreB^2+1)^2*(2*centerScale n K)^4 :=
      mul_le_mul_of_nonneg_left hp4 (by positivity)
    _ = _ := by ring

theorem point_bad_absorption_numeric (u c T : ℝ) (hu : 1 ≤ u) (hc : 0 < c)
    (hT : u^2 + Real.log (2/c) ≤ T) :
    Real.exp (-T) ≤ (c/(2*u))*Real.exp (-(u^2/2)) := by
  have hUp : u ≤ Real.exp (u^2/2) := by
    exact (show u ≤ u^2/2+1 by nlinarith [sq_nonneg (u-1)]).trans (Real.add_one_le_exp _)
  have hu' : 0 < u := by linarith
  calc
    _ ≤ Real.exp (-(u^2 + Real.log (2/c))) := Real.exp_le_exp.mpr (neg_le_neg hT)
    _ = (c/2)*Real.exp (-(u^2)) := by
      rw [neg_add, Real.exp_add, Real.exp_neg (Real.log (2/c)), Real.exp_log (by positivity)]
      field_simp [hc.ne'] <;> ring
    _ ≤ _ := by
      have h0 : u * Real.exp (-(u^2)) ≤ Real.exp (-(u^2/2)) := by
        calc
          _ ≤ Real.exp (u^2/2) * Real.exp (-(u^2)) :=
            mul_le_mul_of_nonneg_right hUp (Real.exp_pos _).le
          _ = _ := by rw [← Real.exp_add]; congr 1 <;> ring
      have hh := mul_le_mul_of_nonneg_left ((le_div_iff₀ hu').2 (by simpa [mul_comm] using h0))
        (show 0 ≤ c/2 by positivity)
      convert hh using 1 <;> ring

theorem one_point_good_actual_bound {n K : ℕ} (hK : 4 ≤ K) (hn : 0 < n) {t : ℝ}
    (hu : 1 ≤ centerScale n K) (hKu : 32*centerScale n K ≤ (K:ℝ))
    (ht : |t-(K:ℝ)/4| ≤ (K:ℝ)/(100*centerScale n K))
    (hN : readyMD n scoreB) (hWin : (2*centerScale n K)^6 ≤ (n:ℝ))
    (hErr : 72*scoreB^3*(2*centerScale n K)^3/Real.sqrt (n:ℝ) ≤ 1)
    (hLoss : centerScale n K^2+Real.log (2/singleLower) ≤
      (n:ℝ)/(32*(scoreB^2+1)^2*centerScale n K^4)) :
    singleLower/(2*centerScale n K) * Real.exp (-(centerScale n K^2/2)) ≤
      (cellLaw n).real (hitPoint n K t) ∧
    (cellLaw n).real (hitPoint n K t) ≤
      singleUpper/centerScale n K * Real.exp (-(centerScale n K^2/2)) := by
  let u := centerScale n K
  let z := pointThreshold n K t
  let G := goodPoint n K t
  let E : Set (Fin n → ℝ) := {v | z ≤ normalizedRow (normalizedScore K t) v}
  let P := cellLaw n
  have ⟨hv, hzl, hzu, hzs, hvu⟩ := physical_threshold_stable hK hu hKu ht
  have hz0 : 0 ≤ z := (by linarith : 0 ≤ u).trans hzl
  have hWin' : z^6 ≤ (n:ℝ) := (pow_le_pow_left₀ hz0 hzu _).trans hWin
  have hB : 0 ≤ scoreB := by unfold scoreB; positivity
  have hErr' : 72*scoreB^3*z^3/Real.sqrt (n:ℝ) ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hz0 hzu (3:ℕ))
      (show 0 ≤ 72*scoreB^3 by positivity)
    exact (div_le_div_of_nonneg_right hh (Real.sqrt_nonneg _)).trans hErr
  have hb := one_point_actual_bound hK hn hu hzl (by linarith only [hzs]) hzu ht hN hWin' hErr'
  have hc : 0 < singleLower := by unfold singleLower; exact div_pos mdLower_pos (by positivity)
  have hG := (point_quadratic_good_bad hK hn hu hKu ht).trans
    (point_bad_absorption_numeric u singleLower _ hu hc hLoss)
  have hEG : E ⊆ (E∩G) ∪ Gᶜ := by
    intro x hx
    by_cases h : x∈G
    · exact Or.inl ⟨hx,h⟩
    · exact Or.inr h
  have hsum := (measureReal_mono (μ := P) hEG).trans (measureReal_union_le (μ := P) (E∩G) Gᶜ)
  change singleLower/(2*u)*Real.exp (-(u^2/2)) ≤ P.real (E∩G) ∧
    P.real (E∩G) ≤ singleUpper/u*Real.exp (-(u^2/2))
  constructor
  · have hl : singleLower/u * Real.exp (-(u^2/2)) ≤ P.real E := hb.1
    have bad : P.real Gᶜ ≤ singleLower/(2*u) * Real.exp (-(u^2/2)) := hG
    have hsplit : singleLower/u * Real.exp (-(u^2/2)) =
      2 * (singleLower/(2*u) * Real.exp (-(u^2/2))) := by ring
    rw [hsplit] at hl
    linarith only [hl, bad, hsum]
  · exact (measureReal_mono inter_subset_left).trans hb.2

end CenteredCube.RudinDensity
#print axioms CenteredCube.RudinDensity.physical_threshold_stable
#print axioms CenteredCube.RudinDensity.point_quadratic_good_bad
#print axioms CenteredCube.RudinDensity.one_point_good_actual_bound
