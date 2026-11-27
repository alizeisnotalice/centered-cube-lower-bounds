import CellMeasure
import TensorAverage
import SqrtLogWiring

open MeasureTheory Set
open scoped ENNReal

namespace CenteredCube

theorem box_event_volume {n : ℕ} (R : ℕ) (E : Set (Space n)) (hE : MeasurableSet E) :
    volume (box n (R:ℝ) ∩ cellRep ⁻¹' E) =
      ENNReal.ofReal ((2*(R:ℝ))^n) * RudinDensity.cellLaw n E := by
  have h := open_box_event_volume (-(R:ℤ)) (2*R) E hE
  have hae : openIntBox n (-(R:ℤ)) (2*R) =ᵐ[(volume : Measure (Space n))] box n (R:ℝ) := by
    unfold openIntBox
    rw [box_eq_pi]
    simp only [Int.cast_neg, Int.cast_natCast, Nat.cast_mul, Nat.cast_ofNat]
    have he : -(R:ℝ)+2*(R:ℝ) = (R:ℝ) := by ring
    rw [he]
    rw [volume_pi]
    exact Measure.pi_Ioc_ae_eq_pi_Icc (μ := fun _ : Fin n => (volume : Measure ℝ))
  have haei : (openIntBox n (-(R:ℤ)) (2*R) ∩ cellRep ⁻¹' E) =ᵐ[
      (volume : Measure (Space n))] box n (R:ℝ) ∩ cellRep ⁻¹' E := by
    filter_upwards [hae] with x hx
    simp only [mem_inter_iff, hx]
  rw [measure_congr haei] at h
  rw [h, ENNReal.ofReal_pow (by positivity), Nat.cast_mul, Nat.cast_ofNat]
  rw [ENNReal.ofReal_mul (by norm_num : 0 ≤ (2:ℝ)), ENNReal.ofReal_natCast]
  norm_num

namespace RudinDensity

noncomputable def haloDataOfProductCell {n K : ℕ} {c u : ℝ}
    (hn : 2 ≤ n) (hK : 1 ≤ K)
    (hheight : Real.log (n:ℝ)-1 ≤ u^2)
    (E : Set (Space n)) (hE : MeasurableSet E)
    (hmass : c / Real.log (n:ℝ) ≤ (cellLaw n).real E)
    (hw : ∀ x ∈ E, ∃ r : ℝ, 0 < r ∧ r ≤ 2 ∧
        ENNReal.ofReal (Real.exp (u^2/2-2)) < cubeAverage (tensorRho K n) x r) :
    HaloData n c := by
  let R : ℕ := n^2-1
  have hr_nat : 1 ≤ n^2 := by nlinarith [show 2 ≤ n from hn]
  have hr : (R:ℝ) = (n:ℝ)^2-1 := by
    dsimp [R]
    rw [Nat.cast_sub hr_nat, Nat.cast_pow, Nat.cast_one]
  refine {
    height := u^2/2-2
    test := tensorRho K n
    halo := box n ((n:ℝ)^2-1) ∩ cellRep ⁻¹' E
    height_ge := by linarith only [hheight]
    integrable := ?_
    mass := ?_
    volume_ge := ?_
    witness := ?_
  }
  · apply (IntegrableOn.integrable_indicator _ (measurableSet_box _ _))
    exact (continuous_tensorRho hK n).integrableOn_Icc
  · have H := absMass_indicator_tensorRho (n := n) hK (n^2)
    simpa only [Nat.cast_pow] using H
  · rw [← hr, box_event_volume R E hE]
    have Heq : 2*(R:ℝ) = 2*(n:ℝ)^2-2 := by rw [hr]; ring
    rw [← Heq, mul_comm (c/Real.log (n:ℝ)), ENNReal.ofReal_mul (by positivity)]
    gcongr
    have hm := ENNReal.ofReal_le_ofReal hmass
    simpa only [Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _)] using hm
  · intro x hx
    obtain ⟨r,hr0,hr2,H⟩ := hw (cellRep x) hx.2
    refine ⟨hx.1,r,hr0,hr2,?_⟩
    have shift_id : (fun i => cellRep x i + (ceilIndex x i:ℝ)) = x := by
      funext i
      simp only [cellRep, cellShift, Pi.sub_apply]
      ring
    have hshift := cubeAverage_tensor_add_int hK (cellRep x) (ceilIndex x) r hr0
    rw [shift_id] at hshift
    rw [hshift]
    exact H

end RudinDensity
end CenteredCube

#print axioms CenteredCube.box_event_volume
#print axioms CenteredCube.RudinDensity.haloDataOfProductCell
