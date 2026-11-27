import GaussianFaceKernel
import GaussianWeakFaces

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology ProbabilityTheory
namespace CubeBrownian

/-- The real weighted face mass after threshold normalization tends to
φ(0) times the limiting Gaussian face probability. The face convergence is
expressed in terms of the actual scalar regression residual law. -/
theorem gaussian_winner_thinLayer_tendsto
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E]
    (μ : ℕ → Measure Ω) [∀ n, IsProbabilityMeasure (μ n)]
    (Z : ℕ → Ω → ℝ) (D : ℕ → Ω → E) (c : ℕ → E)
    (hmZ : ∀ n, Measurable (Z n)) (hmD : ∀ n, Measurable (D n))
    (hZD : ∀ n, HasGaussianLaw (fun w ↦ (Z n w,D n w)) (μ n))
    (hc : ∀ n (L : StrongDual ℝ E), cov[Z n, L ∘ D n; μ n] = L (c n) * Var[Z n; μ n])
    (a u : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (hv : ∀ n, 0 < v n) (hZ : ∀ n, HasLaw (Z n) (gaussianReal (a n) (v n)) (μ n))
    (hu : ∀ n, 0 ≤ u n)
    (hScale : Tendsto (fun n ↦ u n / Real.sqrt (v n:ℝ)) atTop (𝓝 1))
    (hOffset : ∀ x ∈ Ioi (0:ℝ), Tendsto (fun n ↦ (x-a n)/Real.sqrt (v n:ℝ)) atTop (𝓝 0))
    (F : Set E) (hF : MeasurableSet F) {q : ℝ≥0∞} (hq : q ≠ ∞)
    (hFace : ∀ x ∈ Ioi (0:ℝ), Tendsto
      (fun n ↦ (μ n) {w | D n w-Z n w • c n+x • c n ∈ F}) atTop (𝓝 q)) :
    Tendsto (fun n ↦ u n *
      (∫⁻ w in {w | 0 < Z n w ∧ D n w ∈ F}, ENNReal.ofReal (Real.exp (-(Z n w))) ∂(μ n)).toReal)
      atTop (𝓝 (φ 0 * q.toReal)) := by
  let R (n : ℕ) (w : Ω) := D n w-Z n w • c n
  let τ (n : ℕ) := (μ n).map (R n)
  let A (n : ℕ) : Set (ℝ × E) := {p | p.2+p.1 • c n ∈ F}
  let π (n : ℕ) := faceSectionProb (τ n) (A n)
  have hmR n : Measurable (R n) := (hmD n).sub ((hmZ n).smul measurable_const)
  have hA n : MeasurableSet (A n) := (measurable_snd.add (measurable_fst.smul measurable_const)) hF
  letI (n : ℕ) : IsProbabilityMeasure (τ n) :=
    (Measure.isProbabilityMeasure_map_iff (hmR n).aemeasurable).2 inferInstance
  have hmπ n : Measurable (π n) := measurable_faceSectionProb (τ n) (hA n)
  have hπ n x (_ : x ∈ Ioi (0:ℝ)) : 0 ≤ π n x ∧ π n x ≤ 1 :=
    faceSectionProb_mem_Icc (τ n) (A n) x
  have hπeq n x : π n x = ((μ n) {w | D n w-Z n w • c n+x • c n ∈ F}).toReal := by
    dsimp only [π,faceSectionProb,τ]
    have hS : MeasurableSet ((fun y : E ↦ (x,y)) ⁻¹' A n) :=
      (measurable_const.prodMk (measurable_id : Measurable (id : E → E))) (hA n)
    rw [Measure.map_apply (hmR n) hS]
    rfl
  have hπlim (x : ℝ) (hx : x ∈ Ioi (0:ℝ)) : Tendsto (fun n ↦ π n x) atTop (𝓝 q.toReal) := by
    simp_rw [hπeq]
    exact (ENNReal.continuousAt_toReal hq).tendsto.comp (hFace x hx)
  have H := thinLayer_weighted_gaussian_limit u (fun _ ↦ 0) a v π q.toReal hu hv hmπ hπ hScale
    (fun x hx ↦ by simpa only [zero_add] using hOffset x hx) hπlim
  apply H.congr
  intro n
  simp only [zero_add]
  rw [gaussian_weighted_original_face (μ n) (Z n) (D n) (c n) (hmZ n) (hmD n) (hZD n)
    (hc n) (a n) (hv n) (hZ n) F hF]

end CubeBrownian
#print axioms CubeBrownian.gaussian_winner_thinLayer_tendsto
