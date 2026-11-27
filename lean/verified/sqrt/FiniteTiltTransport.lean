import BrownianMaximum
import BrownianFiniteTilt

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
namespace CubeBrownian

theorem map_tilt_composition {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) (D : Ω → Ξ) (g : Ξ → ℝ)
    (hmD : Measurable D) (hmG : Measurable g) :
    (μ.tilted (g ∘ D)).map D = (μ.map D).tilted g := by
  ext s hs
  rw [Measure.map_apply hmD hs, tilted_apply' _ _ (hmD hs), tilted_apply' _ _ hs,
    Measure.restrict_map hmD hs]
  have hN : (∫ x, Real.exp (g x) ∂(μ.map D)) = ∫ x, Real.exp ((g ∘ D) x) ∂μ :=
    integral_map hmD.aemeasurable (Real.measurable_exp.comp hmG).aestronglyMeasurable
  rw [hN]
  rw [lintegral_map (by fun_prop) hmD]
  rfl

theorem dyadicIncrements_centered_law {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)
    (T : ℝ≥0) (r : ℕ) :
    let D := fun w ↦ dyadicIncrements T r (centeredScaled B w)
    let h := T/(2:ℝ≥0)^r
    μ.map D = Measure.pi (fun _ : Fin (2^r) ↦ gaussianReal 0 (2*h)) := by
  dsimp only
  let D := fun w ↦ dyadicIncrements T r (centeredScaled B w)
  let h := T/(2:ℝ≥0)^r
  let t : Fin (2^r+1) → ℝ≥0 := fun i ↦ dyadicT T r i
  have ht : Monotone t := fun _ _ hij ↦ dyadicT_mono T r hij
  have hs : NNReal.mk ((Real.sqrt 2)^2) (sq_nonneg _) = 2 := by
    apply NNReal.eq
    exact Real.sq_sqrt (by norm_num)
  have hd (i : Fin (2^r)) : nndist (t i.succ).1 (t i.castSucc).1 = h := by
    apply NNReal.eq
    change dist (dyadicT T r ((i:ℕ)+1):ℝ) (dyadicT T r i:ℝ) = _
    rw [Real.dist_eq,abs_of_nonneg,dyadicT_succ_sub]
    · rfl
    · exact sub_nonneg.mpr (dyadicT_mono T r (Nat.le_succ _))
  have hD : (fun w (i : Fin (2^r)) ↦ Real.sqrt 2*(B (t i.succ) w-B (t i.castSucc) w)) = D := by
    funext w i
    change Real.sqrt 2*(B (t i.succ) w-B (t i.castSucc) w) =
      Real.sqrt 2*(B (t i.succ) w-B 0 w) - Real.sqrt 2*(B (t i.castSucc) w-B 0 w)
    ring
  have hLaw := brownian_gridLaw hB (Real.sqrt 2) t ht
  rw [hD,hs] at hLaw
  simp_rw [hd] at hLaw
  exact hLaw

theorem dyadicIncrements_tilt_law {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)
    (hmB : ∀ t, Measurable (B t)) (T : ℝ≥0) (hT : 0 < T) (r : ℕ) :
    let D := fun w ↦ dyadicIncrements T r (centeredScaled B w)
    let h := T/(2:ℝ≥0)^r
    (μ.tilted (fun w ↦ -(centeredScaled B w T / 2))).map D =
      Measure.pi (fun _ : Fin (2^r) ↦ gaussianReal (-(h:ℝ)) (2*h)) := by
  dsimp only
  let D := fun w ↦ dyadicIncrements T r (centeredScaled B w)
  let h := T/(2:ℝ≥0)^r
  let t : Fin (2^r+1) → ℝ≥0 := fun i ↦ dyadicT T r i
  have ht : Monotone t := fun _ _ hij ↦ dyadicT_mono T r hij
  have hh : 0 < h := by dsimp [h]; positivity
  have hmF (s : ℝ≥0) : Measurable (fun w ↦ centeredScaled B w s) :=
    measurable_const.mul ((hmB s).sub (hmB 0))
  have hmD : Measurable D :=
    measurable_pi_iff.mpr (fun i ↦ (hmF _).sub (hmF _))
  let g (x : Fin (2^r) → ℝ) : ℝ := (-1/2)*(∑ i, x i)
  have hmFsum : Measurable (fun x : Fin (2^r) → ℝ ↦ ∑ i, x i) :=
    Finset.measurable_fun_sum _ (fun i _ ↦ measurable_pi_apply i)
  have hmG : Measurable g := measurable_const.mul hmFsum
  have hTot (w : Ω) : (∑ i, D w i) = centeredScaled B w T := by
    change (∑ (i : Fin (2^r)), (((centeredScaled B w) ∘ dyadicT T r) ((i:ℕ)+1) -
      ((centeredScaled B w) ∘ dyadicT T r) i)) = _
    rw [total_pathDifferences]
    simp [dyadicT_last,dyadicT_zero,centeredScaled_zero]
  have he : (fun w ↦ -(centeredScaled B w T / 2)) = g ∘ D := by
    funext w
    change -(centeredScaled B w T / 2) = (-1/2)*(∑ i, D w i)
    rw [hTot]
    ring
  change (μ.tilted (fun w ↦ -(centeredScaled B w T / 2))).map D = _
  rw [he,map_tilt_composition μ D g hmD hmG,dyadicIncrements_centered_law μ hB T r]
  exact finite_partition_terminal_tilt (fun _ ↦ h) (fun _ ↦ hh)
end CubeBrownian
#print axioms CubeBrownian.dyadicIncrements_tilt_law
