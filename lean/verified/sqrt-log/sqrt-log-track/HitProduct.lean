import ActualGrowth
import LogTensor

open MeasureTheory Interval Set
namespace CenteredCube.RudinDensity

noncomputable def pointDeviation (K : ℕ) (t x : ℝ) : ℝ :=
  sigma K t * normalizedScore K t x

theorem pointDeviation_eq {K : ℕ} (hK : 0 < K) {t x : ℝ}
    (hr : 0 < rfun K t) (hV : 0 < VK K t) :
    pointDeviation K t x =
      Sfun K t x/(30*Real.pi*(K:ℝ)*Real.sqrt (K:ℝ)*rfun K t) := by
  let D := 30*Real.pi*(K:ℝ)*Real.sqrt (K:ℝ)*rfun K t
  have hK' : 0 < (K:ℝ) := by exact_mod_cast hK
  have hD : 0 < D := by dsimp only [D]; positivity
  have he : D^2 = 900*Real.pi^2*(K:ℝ)^3*(rfun K t)^2 := by
    dsimp only [D]
    rw [mul_pow,mul_pow,mul_pow,mul_pow, Real.sq_sqrt hK'.le]
    ring
  have hσ : sigma K t = Real.sqrt (VK K t)/D := by
    unfold sigma sigmaSq
    rw [← he, Real.sqrt_div hV.le, Real.sqrt_sq hD.le]
  unfold pointDeviation normalizedScore
  rw [hσ]
  change (Real.sqrt (VK K t)/D)*(Sfun K t x/Real.sqrt (VK K t)) = Sfun K t x/D
  field_simp [hD.ne', (Real.sqrt_pos.2 hV).ne'] <;> ring

theorem average_rho_eq_pointDeviation {K : ℕ} (hK : 0 < K) {t x : ℝ}
    (hr : 0 < rfun K t) (hV : 0 < VK K t) :
    1/(rfun K t) * (∫ y in (x-rfun K t/2)..(x+rfun K t/2), rho K y)
      = 1+pointDeviation K t x := by
  rw [pointDeviation_eq hK hr hV]
  exact average_rho (by omega) t x hr

theorem point_log_numeric (n : ℕ) (hn : 0 < n) (B u v : ℝ)
    (hB : 0 ≤ B) (hv : 0 < v) (hvu : v ≤ 2*u)
    (hErr : 72*B^3*(2*u)^3/Real.sqrt (n:ℝ) ≤ 1) :
    B * (v/Real.sqrt (n:ℝ)) ≤ 1/2 ∧
      3*(n:ℝ)*(B*(v/Real.sqrt (n:ℝ)))^3 ≤ 1 := by
  let r := Real.sqrt (n:ℝ)
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hr : 0 < r := Real.sqrt_pos.2 (by positivity)
  have hbv : 0 ≤ B*(v/r) := by positivity
  have hE : 72*B^3*v^3/r ≤ 1 := by
    exact (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hv.le hvu (3:ℕ)) (by positivity))
      hr.le).trans hErr
  have hr3 : r^3 = (n:ℝ)*r := by rw [pow_succ, Real.sq_sqrt (by positivity)]
  have h3 : (B*(v/r))^3 = (B^3*v^3/r)/(n:ℝ) := by
    rw [mul_pow, div_pow, hr3]
    field_simp [hr.ne', (by positivity : (0:ℝ)<n).ne'] <;> ring
  have hE' : B^3*v^3/r ≤ 1/72 := by
    have h : 72 * (B^3*v^3/r) ≤ 1 := by simpa only [mul_div_assoc, mul_assoc] using hE
    linarith
  have hN : 0 < (n:ℝ) := by positivity
  have hc3 : (B*(v/r))^3 ≤ (1/2 : ℝ)^3 := by
    rw [h3]
    apply (div_le_iff₀ hN).2
    nlinarith only [hE', hn']
  constructor
  · exact le_of_pow_le_pow_left₀ (by decide : (3:ℕ) ≠ 0) (by norm_num) hc3
  · rw [h3]
    calc
      _ = 3*(B^3*v^3/r) := by field_simp [hN.ne'] <;> ring
      _ ≤ _ := by linarith

theorem hitPoint_product_witness {n K : ℕ} (hK : 4 ≤ K) (hn : 0 < n) {t : ℝ}
    (hu : 1 ≤ centerScale n K) (hKu : 32*centerScale n K ≤ (K:ℝ))
    (ht : |t-(K:ℝ)/4| ≤ (K:ℝ)/(100*centerScale n K))
    (hErr : 72*scoreB^3*(2*centerScale n K)^3/Real.sqrt (n:ℝ) ≤ 1)
    {x : Fin n → ℝ} (hx : x ∈ hitPoint n K t) :
    Real.exp (centerScale n K^2/2-2) <
      ∏ i, (1+pointDeviation K t (x i)) := by
  let u := centerScale n K
  let v := pointScale n K t
  let z := pointThreshold n K t
  let d : Fin n → ℝ := fun i ↦ pointDeviation K t (x i)
  let r := Real.sqrt (n:ℝ)
  have hr : 0 < r := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hu75 : 3/50 ≤ u := by linarith only [hu]
  have hprop := physical_threshold_stable hK hu hKu ht
  have hv : 0 < v := hprop.1
  have hvu : v ≤ 2*u := hprop.2.2.2.2
  have hS : sigma K t = v/r := by
    change sigma K t = r * sigma K t / r
    field_simp [hr.ne']
  have hB : 0 ≤ scoreB := by unfold scoreB; positivity
  obtain ⟨hmax,hcube⟩ := point_log_numeric n hn scoreB u v hB hv hvu hErr
  have hAbs (i : Fin n) : |d i| ≤ scoreB*(v/r) := by
    change |sigma K t * normalizedScore K t (x i)| ≤ _
    rw [hS, abs_mul, abs_of_pos (div_pos hv hr), mul_comm (v/r)]
    exact mul_le_mul_of_nonneg_right
      (by simpa only [scoreB] using normalizedScore_abs_le hK hu75 ht (x i))
      (by positivity)
  have hLin : u^2/2-2+v^2/2+2 ≤ ∑ i, d i := by
    have hTerm : (fun i ↦ d i) = fun i ↦ (v/r)*normalizedScore K t (x i) := by
      funext i
      dsimp only [d, pointDeviation]
      rw [hS]
    have hh := mul_le_mul_of_nonneg_left (show z ≤ normalizedRow (normalizedScore K t) x from hx.1) hv.le
    have he : v*z = u^2/2-2+v^2/2+2 := by
      dsimp only [z, pointThreshold, CubeMD.singleThreshold]
      change v*((u^2+v^2)/(2*v)) = _
      field_simp [hv.ne'] <;> ring
    have hEq : v*normalizedRow (normalizedScore K t) x = ∑ i, d i := by
      unfold normalizedRow
      rw [hTerm, ← Finset.mul_sum]
      change v * ((∑ i, normalizedScore K t (x i))/r) = _
      ring
    rw [he, hEq] at hh
    exact hh
  have hQuad : ∑ i, (d i)^2 ≤ v^2+1 := by
    have hg : (sigma K t)^2*(∑ i, normalizedScore K t (x i)^2) ≤ v^2+1 := hx.2
    simpa only [d, pointDeviation, mul_pow, ← Finset.mul_sum] using hg
  have hCub : 3 * ∑ i, |d i|^3 ≤ 1 := by
    apply le_trans _ hcube
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    calc
      _ ≤ ∑ _i : Fin n, (scoreB*(v/r))^3 :=
        Finset.sum_le_sum (fun i _ ↦ pow_le_pow_left₀ (abs_nonneg _) (hAbs i) _)
      _ = _ := by simp [r]
  exact CenteredCube.exp_lt_product_of_event d (u^2/2-2) (v^2)
    (fun i ↦ (hAbs i).trans hmax) hLin hQuad hCub

theorem measurableSet_hitPoint (n K : ℕ) (t : ℝ) :
    MeasurableSet (hitPoint n K t) := by
  have hm (i : Fin n) : Measurable (fun x : Fin n → ℝ ↦ normalizedScore K t (x i)) :=
    (normalizedScore_cont K t).measurable.comp (measurable_pi_apply i)
  have hRow : Measurable (normalizedRow (n := n) (normalizedScore K t)) := by
    unfold normalizedRow
    exact (Finset.measurable_fun_sum _ (fun i _ ↦ hm i)).div_const _
  have hSum : Measurable (fun x : Fin n → ℝ ↦ ∑ i, normalizedScore K t (x i)^2) :=
    Finset.measurable_fun_sum (Finset.univ : Finset (Fin n)) (fun i _ ↦ (hm i).pow_const 2)
  have hQ : Measurable (fun x : Fin n → ℝ ↦ (sigma K t)^2 * ∑ i, normalizedScore K t (x i)^2) :=
    measurable_const.mul hSum
  unfold hitPoint goodPoint CubeMD.quadraticGood
  exact (measurableSet_le measurable_const hRow).inter (measurableSet_le hQ measurable_const)

theorem hitPoint_intervalAverage_witness {n K : ℕ} (hK : 4 ≤ K) (hn : 0 < n) {t : ℝ}
    (hu : 1 ≤ centerScale n K) (hKu : 32*centerScale n K ≤ (K:ℝ))
    (ht : |t-(K:ℝ)/4| ≤ (K:ℝ)/(100*centerScale n K))
    (hErr : 72*scoreB^3*(2*centerScale n K)^3/Real.sqrt (n:ℝ) ≤ 1)
    {x : Fin n → ℝ} (hx : x ∈ hitPoint n K t) :
    0 < rfun K t ∧ rfun K t ≤ 2 ∧
    Real.exp (centerScale n K^2/2-2) <
      ∏ i, (1/(rfun K t))*(∫ y in (x i-rfun K t/2)..(x i+rfun K t/2), rho K y) := by
  have hu75 : 3/50 ≤ centerScale n K := by linarith only [hu]
  have hR := rfun_window (by omega : 1 ≤ K) hu75 ht
  have hr : 0 < rfun K t := by linarith only [hR.1]
  have hK' : 0 < (K:ℝ) := by exact_mod_cast (by omega : 0 < K)
  have hV : 0 < VK K t := (by positivity : (0:ℝ)<(K:ℝ)/8).trans_le (VK_window hK hu75 ht).2.1
  refine ⟨hr,by linarith only [hR.2],?_⟩
  simp_rw [average_rho_eq_pointDeviation (by omega : 0 < K) hr hV]
  exact hitPoint_product_witness hK hn hu hKu ht hErr hx

theorem hitPoint_subset_raw {n K : ℕ} (hK : 4 ≤ K) {t : ℝ}
    (hu : 1 ≤ centerScale n K) (hKu : 32*centerScale n K ≤ (K:ℝ))
    (ht : |t-(K:ℝ)/4| ≤ (K:ℝ)/(100*centerScale n K)) :
    hitPoint n K t ⊆ {x : Fin n → ℝ | centerScale n K ≤ normalizedRow (normalizedScore K t) x} := by
  intro x hx
  exact (physical_threshold_stable hK hu hKu ht).2.1.trans hx.1

end CenteredCube.RudinDensity
#print axioms CenteredCube.RudinDensity.pointDeviation_eq
#print axioms CenteredCube.RudinDensity.average_rho_eq_pointDeviation
#print axioms CenteredCube.RudinDensity.point_log_numeric
#print axioms CenteredCube.RudinDensity.hitPoint_product_witness
#print axioms CenteredCube.RudinDensity.hitPoint_intervalAverage_witness
#print axioms CenteredCube.RudinDensity.measurableSet_hitPoint
#print axioms CenteredCube.RudinDensity.hitPoint_subset_raw
