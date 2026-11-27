import BrownianUniformContinuous
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
namespace CubeBrownian

theorem strictPrefix_pathDifferences {n : ℕ} (f : ℕ → ℝ) (k : ℕ) :
    (∑ i : Fin n, if (i:ℕ) < k then f ((i:ℕ)+1)-f i else 0) =
      f (min k n)-f 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun i ↦ if i < k then f (i+1)-f i else 0),
    ← Finset.sum_filter]
  have hs : (Finset.range n).filter (fun i ↦ i < k) = Finset.range (min k n) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, lt_min_iff]
    tauto
  rw [hs,Finset.sum_range_sub]

theorem tilt_sub_const {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → ℝ) (c : ℝ) :
    μ.tilted (fun w ↦ f w-c) = μ.tilted f := by
  unfold Measure.tilted
  have hr : (fun w ↦ Real.exp (f w-c)) = fun w ↦ Real.exp (-c) * Real.exp (f w) := by
    funext w
    rw [sub_eq_add_neg,Real.exp_add,mul_comm]
  conv_lhs => simp only [hr,integral_const_mul]
  congr 1
  funext w
  congr 1
  rw [show Real.exp (f w-c) = Real.exp (-c)*Real.exp (f w) from congrFun hr w]
  exact mul_div_mul_left _ _ (Real.exp_ne_zero _)

theorem gaussian_zero_tilt_eq_shift_all (a : ℝ) (v : ℝ≥0) :
    (gaussianReal 0 v).tilted (fun x ↦ a*x) = gaussianReal (a*(v:ℝ)) v := by
  rcases eq_or_lt_of_le (zero_le : 0 ≤ v) with h | h
  · subst v
    have he : (fun x : ℝ ↦ a*x) =ᵐ[gaussianReal 0 0] (0 : ℝ → ℝ) := by
      rw [gaussianReal_zero_var]
      rw [Filter.EventuallyEq, ae_dirac_iff]
      · simp
      · exact measurableSet_eq_fun (by fun_prop) (by fun_prop)
    rw [tilted_congr he,tilted_zero]
    simp
  · exact gaussian_zero_tilt_eq_shift a v h

noncomputable def anchorGridIncrements {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (c : ℝ)
    {n : ℕ} (t : Fin (n+1) → ℝ≥0) (w : Ω) (i : Fin n) : ℝ :=
  c*(B (t i.succ) w-B (t i.castSucc) w)

theorem brownian_anchor_tilt_grid_law {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)
    (hmB : ∀ s, Measurable (B s)) (c θ : ℝ)
    {n : ℕ} (t : Fin (n+1) → ℝ≥0) (ht : Monotone t) (j : Fin (n+1)) :
    let v (i : Fin n) := NNReal.mk (c^2) (sq_nonneg c) * nndist (t i.succ).1 (t i.castSucc).1
    (μ.tilted (fun w ↦ θ*c*(B (t j) w-B (t 0) w))).map (anchorGridIncrements B c t) =
      Measure.pi (fun (i : Fin n) ↦ gaussianReal (if (i:ℕ) < (j:ℕ) then θ*(v i:ℝ) else 0) (v i)) := by
  dsimp only
  let D := anchorGridIncrements B c t
  let Y (i : Fin n) (x : ℝ) := if (i:ℕ) < (j:ℕ) then x else 0
  let g (x : Fin n → ℝ) := θ * ∑ i, Y i (x i)
  let v (i : Fin n) := NNReal.mk (c^2) (sq_nonneg c) * nndist (t i.succ).1 (t i.castSucc).1
  have hmD : Measurable D := measurable_pi_iff.mpr (fun i ↦ measurable_const.mul ((hmB (t i.succ)).sub (hmB (t i.castSucc))))
  have hmY (i : Fin n) : Measurable (Y i) := by
    by_cases h : (i:ℕ)<(j:ℕ)
    · simpa only [Y,ite_eq_left h] using (show Measurable (fun x : ℝ ↦ x) from measurable_id)
    · simpa only [Y,ite_eq_right h] using (measurable_const : Measurable (fun _ : ℝ ↦ (0:ℝ)))
  have hms : Measurable (fun x : Fin n → ℝ ↦ ∑ i, Y i (x i)) :=
    Finset.measurable_fun_sum _ (fun i _ ↦ (hmY i).comp (measurable_pi_apply i))
  have hmg : Measurable g := measurable_const.mul hms
  have hTel (w : Ω) : (∑ i, Y i (D w i)) = c*(B (t j) w-B (t 0) w) := by
    let f (k : ℕ) := c * B (t ⟨min k n, by omega⟩) w
    have H := strictPrefix_pathDifferences (n:=n) f j
    have hv (i : Fin n) : f ((i:ℕ)+1)-f i = D w i := by
      have hi : (i:ℕ) < n := i.isLt
      simp only [f,min_eq_left (by omega : (i:ℕ)+1 ≤ n),min_eq_left hi.le,D, anchorGridIncrements]
      change c * B (t i.succ) w - c * B (t i.castSucc) w = _
      ring
    change (∑ i : Fin n, if (i:ℕ)<(j:ℕ) then D w i else 0) = _
    simp_rw [hv] at H
    rw [H]
    have hj : (j:ℕ) ≤ n := by omega
    simp only [f,min_eq_left hj,zero_min]
    change c * B (t j) w - c * B (t 0) w = _
    ring
  have he : (fun w ↦ θ * c * (B (t j) w-B (t 0) w)) = g ∘ D := by
    funext w
    change θ*c*_ = θ*(∑ i, Y i (D w i))
    rw [hTel]
    ring
  have hDlaw : μ.map D = Measure.pi (fun i ↦ gaussianReal 0 (v i)) := brownian_gridLaw hB c t ht
  have hInt (i : Fin n) : Integrable (fun x ↦ Real.exp (θ*Y i x)) (gaussianReal 0 (v i)) := by
    by_cases h : (i:ℕ)<(j:ℕ)
    · simpa only [Y,ite_eq_left h] using (integrable_exp_mul_gaussianReal (μ:=0) (v:=v i) θ)
    · simp [Y,h]
  rw [he,map_tilt_composition μ D g hmD hmg,hDlaw,
    CubeMD.tilted_pi_eq_pi_tilted (fun i ↦ gaussianReal 0 (v i)) Y θ hInt]
  congr 1
  funext i
  by_cases h : (i:ℕ)<(j:ℕ)
  · simpa only [Y,ite_eq_left h] using gaussian_zero_tilt_eq_shift_all θ (v i)
  · simp [Y,h,v]
end CubeBrownian
#print axioms CubeBrownian.brownian_anchor_tilt_grid_law
