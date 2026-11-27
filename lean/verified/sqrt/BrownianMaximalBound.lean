import BrownianMeasurableVersion
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
namespace CubeBrownian

theorem gaussian_upper_chernoff (T : ℝ≥0) (hT : 0 < T) (x : ℝ) (hx : 0 ≤ x) :
    gaussianReal 0 (2*T) (Ioi x) ≤ ENNReal.ofReal (Real.exp (-(x^2)/(4*(T:ℝ)))) := by
  rw [gaussianReal_upper_tail 0 x (by positivity : 0 < 2*T),zero_sub]
  have ht : 0 < (T:ℝ) := by exact_mod_cast hT
  have hs : 0 < Real.sqrt (2*(T:ℝ)) := by positivity
  push_cast
  let a := -x/Real.sqrt (2*(T:ℝ))
  have ha : a ≤ 0 := div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hx) hs.le
  apply ENNReal.ofReal_le_ofReal
  calc
    Φ a ≤ Real.exp (-a*a+a^2/2) := Φ_le_exp_tilt a a ha
    _ = Real.exp (-(x^2)/(4*(T:ℝ))) := by
      congr 1
      dsimp only [a]
      have hsq : (Real.sqrt (2*(T:ℝ)))^2 = 2*(T:ℝ) := Real.sq_sqrt (by positivity)
      rw [show -(-x / Real.sqrt (2*(T:ℝ))) * (-x / Real.sqrt (2*(T:ℝ))) +
        (-x / Real.sqrt (2*(T:ℝ)))^2/2 =
        -(x^2)/((Real.sqrt (2*(T:ℝ)))^2*2) by field_simp; ring]
      rw [hsq]
      congr 1
      ring

theorem brownian_positive_sup_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B μ)
    (hmB : ∀ t, Measurable (B t)) (T : ℝ≥0) (hT : 0 < T) (x : ℝ) (hx : 0 ≤ x) :
    μ {w | ∃ t ≤ T, x < centeredScaled B w t} =
      2 * (gaussianReal 0 (2*T)) (Ioi x) := by
  let M := brownianGridMax B T
  let Z := fun w ↦ centeredScaled B w T
  have hmM : Measurable M := measurable_brownianGridMax B hmB T
  have hmZ : Measurable Z := measurable_const.mul ((hmB T).sub (hmB 0))
  have hS : {w | x < M w} =ᵐ[μ] {w | ∃ t ≤ T, x < centeredScaled B w t} := hB.cont.mono (fun w hw ↦ (brownianGridMax_spec B w hT hw).2 x)
  have hEq := brownian_jointEndpointReflection μ hB hmB T hT M hmM
    (hB.cont.mono (fun w hw y _ ↦ (brownianGridMax_spec B w hT hw).2 y)) x hx
  have H := congrArg (fun m : Measure ℝ ↦ m univ) hEq
  let E := {w | x < M w}
  let R : ℝ → ℝ := fun y ↦ 2*x-y
  have hmR : Measurable R := by dsimp [R]; fun_prop
  change (Measure.map Z (μ.restrict E)) univ =
    (Measure.restrict (gaussianReal 0 (2*T)) (Ioi x) +
      (Measure.restrict (gaussianReal 0 (2*T)) (Ioi x)).map R) univ at H
  rw [Measure.map_apply hmZ MeasurableSet.univ,preimage_univ,
    Measure.restrict_apply MeasurableSet.univ,univ_inter,
    add_apply,Measure.map_apply hmR MeasurableSet.univ,preimage_univ,
    Measure.restrict_apply MeasurableSet.univ,univ_inter] at H
  exact (measure_congr hS.symm).trans (H.trans (two_mul _).symm)

theorem brownian_absolute_max_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B μ)
    (hmB : ∀ t, Measurable (B t)) (T : ℝ≥0) (hT : 0 < T) (x : ℝ) (hx : 0 ≤ x) :
    μ {w | ∃ t ≤ T, x < |centeredScaled B w t|} ≤
      4 * ENNReal.ofReal (Real.exp (-(x^2)/(4*(T:ℝ)))) := by
  let E := {w | ∃ t ≤ T, x < centeredScaled B w t}
  let F := {w | ∃ t ≤ T, x < centeredScaled (-B) w t}
  have hN (w : Ω) (t : ℝ≥0) : centeredScaled (-B) w t = -centeredScaled B w t := by
    simp only [centeredScaled,Pi.neg_apply]
    ring
  have he : {w | ∃ t ≤ T, x < |centeredScaled B w t|} = E ∪ F := by
    ext w
    simp only [E,F,mem_union,mem_ofPred_eq,hN,lt_abs]
    exact ⟨fun ⟨t,ht,h⟩ ↦ by rcases h with h|h; exacts [Or.inl ⟨t,ht,h⟩,Or.inr ⟨t,ht,by linarith⟩],
      fun h ↦ by rcases h with ⟨t,ht,h⟩|⟨t,ht,h⟩; exacts [⟨t,ht,Or.inl h⟩, ⟨t,ht,Or.inr (by linarith)⟩]⟩
  rw [he]
  calc
    μ (E ∪ F) ≤ μ E + μ F := measure_union_le E F
    _ = 4 * gaussianReal 0 (2*T) (Ioi x) := by
      unfold E F
      rw [brownian_positive_sup_tail μ hB hmB T hT x hx,
        brownian_positive_sup_tail μ hB.neg (fun t ↦ (hmB t).neg) T hT x hx]
      rw [← add_mul]
      norm_num
    _ ≤ _ := mul_le_mul' (le_refl _) (gaussian_upper_chernoff T hT x hx)
end CubeBrownian
#print axioms CubeBrownian.brownian_absolute_max_bound
