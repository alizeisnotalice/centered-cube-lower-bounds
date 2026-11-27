import Mathlib
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
namespace CubeBrownian

noncomputable def partialSum {n : ℕ} (k : ℕ) (x : Fin n → ℝ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin n ↦ (i:ℕ) ≤ k), x i

def reflectAfter {n : ℕ} (k : ℕ) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i ↦ if (i:ℕ) ≤ k then x i else -x i

def firstCross {n : ℕ} (a : ℝ) (k : ℕ) : Set (Fin n → ℝ) :=
  {x | a < partialSum k x ∧ ∀ j < k, partialSum j x ≤ a}

lemma measurable_partialSum {n : ℕ} (k : ℕ) : Measurable (partialSum (n:=n) k) :=
  Finset.measurable_fun_sum _ (fun i _ ↦ measurable_pi_apply i)

lemma measurable_reflectAfter {n : ℕ} (k : ℕ) : Measurable (reflectAfter (n := n) k) := by
  apply measurable_pi_iff.mpr
  intro i
  by_cases h : (i:ℕ) ≤ k
  · simpa only [reflectAfter,if_pos h] using (measurable_pi_apply i)
  · have he : (fun x : Fin n → ℝ ↦ reflectAfter k x i) = fun x ↦ -x i := by
      funext x; simp only [reflectAfter, if_neg h]
    rw [he]
    exact measurable_neg.comp (measurable_pi_apply i)

lemma measurable_firstCross {n : ℕ} (a : ℝ) (k : ℕ) : MeasurableSet (firstCross (n:=n) a k) := by
  have hS : firstCross (n:=n) a k =
      {x | a < partialSum k x} ∩ ⋂ j : ℕ, {x | j < k → partialSum j x ≤ a} := by
    ext x
    simp [firstCross]
  rw [hS]
  refine (measurableSet_lt measurable_const (measurable_partialSum k)).inter (.iInter (fun j ↦ ?_))
  by_cases h : j < k
  · simpa only [h,true_imp_iff] using
      (measurableSet_le (measurable_partialSum (n:=n) j) (measurable_const (a:=a)))
  · simp [h]

lemma partialSum_reflect {n j k : ℕ} (hjk : j ≤ k) (x : Fin n → ℝ) :
    partialSum j (reflectAfter k x) = partialSum j x := by
  unfold partialSum
  apply Finset.sum_congr rfl
  intro i hi
  exact if_pos ((Finset.mem_filter.mp hi).2.trans hjk)

lemma total_reflect {n : ℕ} (k : ℕ) (x : Fin n → ℝ) :
    (∑ i, reflectAfter k x i) = 2*partialSum k x - ∑ i, x i := by
  have h := Finset.sum_filter_add_sum_filter_not
    (s := Finset.univ) (p := fun i : Fin n ↦ (i:ℕ) ≤ k) (f := x)
  have he (i : Fin n) :
      reflectAfter k x i = (if (i:ℕ) ≤ k then x i else 0) -
        (if ¬ (i:ℕ) ≤ k then x i else 0) := by
    by_cases hi : (i:ℕ) ≤ k <;> simp [reflectAfter,hi]
  simp_rw [he, Finset.sum_sub_distrib, ← Finset.sum_filter]
  unfold partialSum
  linarith only [h]

theorem firstCross_reflect_preimage {n : ℕ} (a : ℝ) (k : ℕ) :
    reflectAfter (n:=n) k ⁻¹' firstCross a k = firstCross a k := by
  ext x
  change (a < partialSum k (reflectAfter k x) ∧ ∀ j < k, partialSum j (reflectAfter k x) ≤ a) ↔ _
  constructor <;> rintro ⟨h₁,h₂⟩ <;> refine ⟨?_, ?_⟩
  · simpa only [partialSum_reflect le_rfl] using h₁
  · intro j hj
    simpa only [partialSum_reflect hj.le] using h₂ j hj
  · simpa only [partialSum_reflect le_rfl] using h₁
  · intro j hj
    simpa only [partialSum_reflect hj.le] using h₂ j hj

theorem reflectAfter_preserves_gaussian {n : ℕ} (v : Fin n → ℝ≥0) (k : ℕ) :
    MeasurePreserving (reflectAfter k) (Measure.pi (fun i ↦ gaussianReal 0 (v i)))
      (Measure.pi (fun i ↦ gaussianReal 0 (v i))) where
  measurable := measurable_reflectAfter k
  map_eq := by
    let f : Fin n → ℝ → ℝ := fun i x ↦ if (i:ℕ) ≤ k then x else -x
    have hm (i : Fin n) : Measurable (f i) := by
      by_cases hi : (i:ℕ) ≤ k
      · have he : f i = id := by funext x; simp [f,hi]
        rw [he]
        exact measurable_id
      · have he : f i = fun x ↦ -x := by funext x; simp [f,hi]
        rw [he]
        exact measurable_neg
    have hmap (i : Fin n) : (gaussianReal 0 (v i)).map (f i) = gaussianReal 0 (v i) := by
      by_cases hi : (i:ℕ) ≤ k
      · simp [f,hi]
      · simp only [f,if_neg hi,gaussianReal_map_neg,neg_zero]
    haveI : ∀ i, SigmaFinite ((gaussianReal 0 (v i)).map (f i)) := fun i ↦ by
      rw [hmap]
      infer_instance
    change (Measure.pi (fun i ↦ gaussianReal 0 (v i))).map (fun x i ↦ f i (x i)) = _
    rw [Measure.pi_map_pi (fun i ↦ (hm i).aemeasurable)]
    simp only [hmap]

theorem reflectAfter_preserves_firstCross_restriction {n : ℕ}
    (v : Fin n → ℝ≥0) (a : ℝ) (k : ℕ) :
    ((Measure.pi (fun i ↦ gaussianReal 0 (v i))).restrict (firstCross a k)).map (reflectAfter k)
      = (Measure.pi (fun i ↦ gaussianReal 0 (v i))).restrict (firstCross a k) := by
  let P := Measure.pi (fun i ↦ gaussianReal 0 (v i))
  let A := firstCross (n:=n) a k
  let R := reflectAfter (n:=n) k
  have hM : Measurable R := measurable_reflectAfter k
  have hA : MeasurableSet A := measurable_firstCross a k
  have hE : R ⁻¹' A = A := firstCross_reflect_preimage a k
  ext s hs
  change ((P.restrict A).map R) s = (P.restrict A) s
  rw [Measure.map_apply hM hs, Measure.restrict_apply (hM hs), Measure.restrict_apply hs]
  calc
    _ = (P.map R) (s ∩ A) := by
      rw [Measure.map_apply hM (hs.inter hA), Set.preimage_inter, hE]
    _ = _ := by rw [(reflectAfter_preserves_gaussian v k).map_eq]

theorem firstCross_endpoint_reflection {n : ℕ} (v : Fin n → ℝ≥0) (a : ℝ) (k : ℕ) :
    let P := (Measure.pi (fun i ↦ gaussianReal 0 (v i))).restrict (firstCross a k)
    P.map (fun x ↦ ∑ i, x i) =
      P.map (fun x ↦ 2*partialSum k x - ∑ i, x i) := by
  dsimp only
  let P := (Measure.pi (fun i ↦ gaussianReal 0 (v i))).restrict (firstCross a k)
  have hTotal : Measurable (fun x : Fin n → ℝ ↦ ∑ i, x i) :=
    Finset.measurable_fun_sum _ (fun i _ ↦ measurable_pi_apply i)
  change P.map (fun x ↦ ∑ i, x i) = _
  have he : (fun x : Fin n → ℝ ↦ 2*partialSum k x - ∑ i, x i) =
      (fun x ↦ ∑ i, x i) ∘ reflectAfter k := funext (fun x ↦ (total_reflect k x).symm)
  rw [he, ← Measure.map_map hTotal (measurable_reflectAfter k)]
  exact congrArg (Measure.map (fun x : Fin n → ℝ ↦ ∑ i, x i))
    (reflectAfter_preserves_firstCross_restriction v a k).symm
end CubeBrownian
#print axioms CubeBrownian.firstCross_endpoint_reflection
