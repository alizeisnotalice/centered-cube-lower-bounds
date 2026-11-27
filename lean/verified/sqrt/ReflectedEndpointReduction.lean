import ExpectationOfTail
import GaussianTilt
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
namespace CubeBrownian

theorem gaussianReal_upper_tail (m x : ℝ) {v : ℝ≥0} (hv : 0 < v) :
    gaussianReal m v (Ioi x) =
      ENNReal.ofReal (Φ ((m-x)/Real.sqrt (v:ℝ))) := by
  let s := Real.sqrt (v:ℝ)
  let g := fun y : ℝ ↦ (m-y)/s
  let u := (m-x)/s
  have hvR : 0 < (v:ℝ) := by exact_mod_cast hv
  have hs : 0 < s := Real.sqrt_pos.2 hvR
  have hm : Measurable g := by dsimp [g]; fun_prop
  have hmap : (gaussianReal m v).map g = gaussianReal 0 1 := by
    have he : g = (fun y : ℝ ↦ y/s) ∘ (fun y ↦ -y) ∘ (fun y ↦ y-m) := by
      funext y
      simp only [g,Function.comp_apply]
      rw [neg_sub]
    rw [he,← Measure.map_map (by fun_prop) (by fun_prop),← Measure.map_map (by fun_prop) (by fun_prop),
      gaussianReal_map_sub_const,sub_self,gaussianReal_map_neg,neg_zero,gaussianReal_map_div_const,zero_div]
    have hh : NNReal.mk (s^2) (sq_nonneg _) = v := by
      apply NNReal.eq
      exact Real.sq_sqrt hvR.le
    rw [hh,div_self hv.ne']
  have hpre : g ⁻¹' Iio u = Ioi x := by
    ext y
    change (m-y)/s < (m-x)/s ↔ x < y
    rw [div_lt_div_iff_of_pos_right hs]
    constructor <;> intro h <;> linarith
  have hno : gaussianReal 0 1 {u} = 0 :=
    gaussianReal_absolutelyContinuous 0 one_ne_zero (measure_singleton u)
  have he : gaussianReal 0 1 (Iio u) = gaussianReal 0 1 (Iic u) :=
    measure_congr (Iio_ae_eq_Iic' hno)
  calc
    _ = (gaussianReal m v).map g (Iio u) := by rw [Measure.map_apply hm measurableSet_Iio,hpre]
    _ = _ := by
      rw [hmap,he]
      change gaussianReal 0 1 (Iic u) = ENNReal.ofReal (Φ u)
      unfold Φ
      rw [cdf_eq_real,Measure.real,ENNReal.ofReal_toReal (measure_ne_top _ _)]

def HasTiltedEndpointSplit {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω)
    (M : Ω → ℝ) (T : ℝ≥0) : Prop :=
  ∀ x ≥ 0, ν {w | x < M w} =
    ((gaussianReal 0 (2*T)).tilted (fun z ↦ -(z/2))) (Ioi x) +
      ENNReal.ofReal (Real.exp (-x)) * (((gaussianReal 0 (2*T)).tilted (fun z ↦ z/2)) (Ioi x))

theorem reflected_tail_of_endpoint_split {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω)
    (M : Ω → ℝ) (T : ℝ≥0) (hT : 0 < T)
    (h : HasTiltedEndpointSplit ν M T) :
    HasReflectedTail ν M (T:ℝ) := by
  intro x hx
  have hpos : (gaussianReal 0 (2*T)).tilted (fun z ↦ z/2) =
      gaussianReal (T:ℝ) (2*T) := by
    have H := gaussian_zero_tilt_eq_shift (1/2) (2*T) (by positivity)
    simp only [NNReal.coe_mul,NNReal.coe_ofNat] at H
    convert H using 2 <;> try ring
  rw [h x hx,endpoint_brownian_tilt T hT,hpos,gaussianReal_upper_tail _ _ (by positivity),
    gaussianReal_upper_tail _ _ (by positivity)]
  push_cast
  have hΦ (u : ℝ) : 0 ≤ Φ u := cdf_nonneg _ _
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,← ENNReal.ofReal_add (hΦ _) (mul_nonneg (Real.exp_pos _).le (hΦ _))]
  rw [show -(T:ℝ)-x = -(x+(T:ℝ)) by ring]
end CubeBrownian
#print axioms CubeBrownian.gaussianReal_upper_tail
#print axioms CubeBrownian.reflected_tail_of_endpoint_split
