import PolyhedralSandwich
import Mathlib.Probability.Distributions.Gaussian.Real

open Set MeasureTheory ProbabilityTheory
open scoped NNReal

namespace CubeSqrtProbability

theorem face_event_subset_union_strips {Ω ι : Type*}
    (G : Ω → ι → ℝ) (strict : ι → Bool) (c : ι → ℝ) (t u : ℝ) :
    faceEvent G strict c u ⊆ faceEvent G strict c t ∪
      ⋃ i, {w | G w i ∈ Icc (c i+t) (c i+u)} := by
  classical
  intro w hw
  by_cases hp : w ∈ faceEvent G strict c t
  · exact Or.inl hp
  · right
    change ¬ ∀ i, facePass (strict i) (G w i) (c i+t) at hp
    obtain ⟨i, hi⟩ := not_forall.mp hp
    apply mem_iUnion.mpr
    refine ⟨i,?_⟩
    have h := hw i
    change c i+t ≤ G w i ∧ G w i ≤ c i+u
    cases hs : strict i
    · simp [facePass,hs] at hi h
      exact ⟨hi.le,h⟩
    · simp [facePass,hs] at hi h
      exact ⟨hi,h.le⟩

theorem gaussianReal_measureReal_Icc_le (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0)
    {a b : ℝ} (hab : a ≤ b) :
    (gaussianReal m v).real (Icc a b) ≤ (b-a)*(√(2*Real.pi*(v:ℝ)))⁻¹ := by
  let C := (√(2*Real.pi*(v:ℝ)))⁻¹
  rw [MeasureTheory.measureReal_def, gaussianReal_apply_eq_integral _ hv,
     ENNReal.toReal_ofReal (integral_nonneg (gaussianPDFReal_nonneg _ _))]
  have hConst : IntegrableOn (fun _ : ℝ ↦ C) (Icc a b) :=
    integrableOn_const (Real.volume_Icc (a := a) (b := b) ▸ ENNReal.ofReal_ne_top)
  calc
    _ ≤ ∫ x in Icc a b, C := by
      apply setIntegral_mono_on (integrable_gaussianPDFReal _ _).integrableOn hConst measurableSet_Icc
      intro x _
      unfold gaussianPDFReal C
      have he : Real.exp (-(x-m)^2 / (2*(v:ℝ))) ≤ 1 :=
        Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by positivity))
      exact mul_le_of_le_one_right (by positivity) he
    _ = _ := by
      rw [setIntegral_const,smul_eq_mul,measureReal_def,Real.volume_Icc,
        ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]

theorem gaussian_face_event_strip_gain {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (G : Ω → ι → ℝ) (strict : ι → Bool)
    (c m : ι → ℝ) (v : ι → ℝ≥0) (hv : ∀ i, v i ≠ 0)
    (hG : ∀ i, Measurable (fun w ↦ G w i))
    (hLaw : ∀ i, ν.map (fun w ↦ G w i) = gaussianReal (m i) (v i))
    {t u : ℝ} (htu : t ≤ u) :
    ν.real (faceEvent G strict c u) - ν.real (faceEvent G strict c t) ≤
      (u-t) * ∑ i, (√(2*Real.pi*(v i:ℝ)))⁻¹ := by
  let A := fun i ↦ {w | G w i ∈ Icc (c i+t) (c i+u)}
  have h₁ := measureReal_mono (μ := ν) (face_event_subset_union_strips G strict c t u)
  have h₂ := measureReal_union_le (μ := ν) (faceEvent G strict c t) (⋃ i, A i)
  have h₃ := measureReal_iUnion_fintype_le (μ := ν) A
  have hEach (i : ι) : ν.real (A i) ≤ (u-t)*(√(2*Real.pi*(v i:ℝ)))⁻¹ := by
    have h := gaussianReal_measureReal_Icc_le (m i) (hv i) (a := c i+t) (b := c i+u) (by linarith)
    have hMap : ν.real (A i) = (gaussianReal (m i) (v i)).real (Icc (c i+t) (c i+u)) := by
      rw [← hLaw i, measureReal_def, measureReal_def, Measure.map_apply (hG i) measurableSet_Icc]
      rfl
    have hd : c i + u - (c i + t) = u-t := by ring
    rw [hMap]
    simpa only [hd] using h
  have h₄ := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ hEach i)
  rw [← Finset.mul_sum] at h₄
  change ν.real (faceEvent G strict c u) ≤
    ν.real (faceEvent G strict c t ∪ ⋃ i, A i) at h₁
  linarith

end CubeSqrtProbability
#print axioms CubeSqrtProbability.gaussian_face_event_strip_gain
