import SqrtRawNearRepresentation
namespace CenteredCubeSqrt
open MeasureTheory Set
open scoped Interval BigOperators
set_option maxHeartbeats 1200000

noncomputable def cellEnergyOn {B : ℕ} (y : Fin B) (a b : ℝ) : ℝ :=
    ∫ r in a..b,(cellPrimitive (labelCellMidpoint y) r)^2

theorem cellEnergy_intervalIntegrable {B : ℕ} (y : Fin B) {a b : ℝ}
    (ha : 0≤a) (hb : b≤1) (hab : a≤b) :
    IntervalIntegrable (fun r => (cellPrimitive (labelCellMidpoint y) r)^2) volume a b := by
  have H := labelCellPrimitive_prod_intervalIntegrable (y,y) (s:=0) hab ha hb
    (by simpa only [add_zero] using ha) (by simpa only [add_zero] using hb)
  simpa only [pow_two,add_zero] using H

theorem cellEnergyOn_adjacent {B : ℕ} (y : Fin B) {a : ℝ} (ha : a∈Icc (0:ℝ) 1) :
    cellEnergyOn y 0 a+cellEnergyOn y a 1=cellEnergyOn y 0 1 := by
  unfold cellEnergyOn
  exact intervalIntegral.integral_add_adjacent_intervals
    (cellEnergy_intervalIntegrable y (by norm_num) ha.2 ha.1)
    (cellEnergy_intervalIntegrable y ha.1 (by norm_num) ha.2)

theorem cell_pair_moment_young {B : ℕ} (y w : Fin B) {a b s : ℝ}
    (hab : a≤b) (h1 : 0≤a) (h2 : b≤1) (h3 : 0≤a+s) (h4 : b+s≤1) :
    |∫ r in a..b,cellPrimitive (labelCellMidpoint y) r*
      cellPrimitive (labelCellMidpoint w) (r+s)| ≤
    (cellEnergyOn y a b+cellEnergyOn w (a+s) (b+s))/2 := by
  let F := cellPrimitive (labelCellMidpoint y)
  let G := cellPrimitive (labelCellMidpoint w)
  have iF : IntervalIntegrable (fun r => (F r)^2) volume a b :=
    cellEnergy_intervalIntegrable y h1 h2 hab
  have iG : IntervalIntegrable (fun r => (G (r+s))^2) volume a b := by
    have h := (cellEnergy_intervalIntegrable w h3 h4 (by linarith : a+s≤b+s)).comp_add_right s
    rwa [add_sub_cancel_right,add_sub_cancel_right] at h
  have iFG : IntervalIntegrable (fun r => ((F r)^2+(G (r+s))^2)/2) volume a b :=
    (iF.add iG).div_const 2
  have p (r : ℝ) : ‖F r*G (r+s)‖≤((F r)^2+(G (r+s))^2)/2 := by
    rw [Real.norm_eq_abs,abs_mul]
    nlinarith [sq_nonneg (|F r|-|G (r+s)|),sq_abs (F r),sq_abs (G (r+s))]
  have h := intervalIntegral.norm_integral_le_of_norm_le hab
      (Filter.Eventually.of_forall (fun r _ => p r)) iFG
  rw [Real.norm_eq_abs,intervalIntegral.integral_div,intervalIntegral.integral_add iF iG,
    intervalIntegral.integral_comp_add_right (f:=fun x => (G x)^2) (a:=a) (b:=b) s] at h
  exact h

theorem rawNearMain_abs_energy_bound {B : ℕ} (hB : 0<B) {θ : ℝ} (hθ : θ∈Icc (0:ℝ) 1) :
    |rawNearMain B θ|≤1/6-1/(12*(B:ℝ)^2) := by
  let a := 1-θ
  let L (y : Fin B) := rawCellMomentLeft θ (y,y)
  let R (p : Fin B×Fin B) := rawCellMomentRight θ p
  let W (y : Fin B) := cellEnergyOn y 0 a+cellEnergyOn y θ 1
  let V (y : Fin B) := cellEnergyOn y a 1+cellEnergyOn y 0 θ
  have ha : a∈Icc (0:ℝ) 1 := ⟨by dsimp [a]; linarith [hθ.2],by dsimp [a]; linarith [hθ.1]⟩
  have hb : 0<(B:ℝ) := by exact_mod_cast hB
  have hL (y : Fin B) : |L y|≤W y/2 := by
    have h := cell_pair_moment_young y y (a:=0) (b:=a) (s:=θ) ha.1 (by norm_num) ha.2
      (by simpa only [zero_add] using hθ.1) (by dsimp [a]; linarith)
    rw [zero_add,show a+θ=1 by dsimp [a]; ring] at h
    exact h
  have hR (p : Fin B×Fin B) : |R p|≤(cellEnergyOn p.1 a 1+cellEnergyOn p.2 0 θ)/2 := by
    have h := cell_pair_moment_young p.1 p.2 (a:=a) (b:=1) (s:=θ-1) ha.2 ha.1 (by norm_num)
      (by dsimp [a]; linarith) (by linarith [hθ.2])
    rw [show a+(θ-1)=0 by dsimp [a]; ring,show 1+(θ-1)=θ by ring] at h
    simp_rw [←add_sub_assoc] at h
    exact h
  have LL : |(1/(B:ℝ))*(∑ y : Fin B,L y)|≤(1/(2*(B:ℝ)))*(∑ y : Fin B,W y) := by
    rw [abs_mul,abs_of_nonneg (by positivity : 0≤1/(B:ℝ))]
    have h := (Finset.abs_sum_le_sum_abs L (Finset.univ : Finset (Fin B))).trans (Finset.sum_le_sum (fun y _ => hL y))
    refine (mul_le_mul_of_nonneg_left h (by positivity)).trans_eq ?_
    rw [←Finset.sum_div]
    ring
  have RR : |(1/(B:ℝ)^2)*(∑ p : Fin B×Fin B,R p)|≤(1/(2*(B:ℝ)))*(∑ y : Fin B,V y) := by
    rw [abs_mul,abs_of_nonneg (by positivity : 0≤1/(B:ℝ)^2)]
    have h := (Finset.abs_sum_le_sum_abs R (Finset.univ : Finset (Fin B×Fin B))).trans (Finset.sum_le_sum (fun p _ => hR p))
    refine (mul_le_mul_of_nonneg_left h (by positivity)).trans_eq ?_
    rw [←Finset.sum_div,Finset.sum_add_distrib,Fintype.sum_prod_type,Fintype.sum_prod_type]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    rw [←Finset.mul_sum]
    unfold V
    rw [Finset.sum_add_distrib]
    field_simp
  change |(1/(B:ℝ))*(∑ y : Fin B,L y)+(1/(B:ℝ)^2)*(∑ p : Fin B×Fin B,R p)|≤_
  refine (abs_add_le _ _).trans ((add_le_add LL RR).trans_eq ?_)
  rw [←mul_add,←Finset.sum_add_distrib]
  have e (y : Fin B) : W y+V y=2*cellEnergyOn y 0 1 := by
    unfold W V
    linarith [cellEnergyOn_adjacent y ha,cellEnergyOn_adjacent y hθ]
  simp_rw [e,←Finset.mul_sum]
  rw [show (1/(2*(B:ℝ)))*(2*(∑ y : Fin B,cellEnergyOn y 0 1))=
    (1/(B:ℝ))*(∑ y : Fin B,cellEnergyOn y 0 1) by ring]
  exact one_cell_average_raw_energy hB

#print axioms rawNearMain_abs_energy_bound
end CenteredCubeSqrt
