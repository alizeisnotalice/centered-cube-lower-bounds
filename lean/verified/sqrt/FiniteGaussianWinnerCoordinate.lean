import GaussianWinnerRawLimitTwoSpaces
import IsonormalEuclidWinner
import WeightedWinnerComparison
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

open MeasureTheory ProbabilityTheory Filter Set WithLp
open scoped NNReal ENNReal Topology ProbabilityTheory RealInnerProductSpace
namespace CubeBrownian

/-- Single winner's actual Gaussian limit at fixed finite separated nodes, in
terms of the *unconditioned* Gaussian companion moments. -/
theorem finiteGaussianWinner_coordinate_tendsto
    {Ω Ω' H : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {N : ℕ} (j : Fin N)
    (μ : ℕ → Measure Ω) (ν : Measure Ω')
    [∀ n, IsProbabilityMeasure (μ n)] [IsProbabilityMeasure ν]
    (Z : ℕ → Ω → ℝ) (D : ℕ → Ω → EuclideanSpace ℝ (Fin N))
    (c : ℕ → EuclideanSpace ℝ (Fin N))
    (hmZ : ∀ n, Measurable (Z n)) (hmD : ∀ n, Measurable (D n))
    (hZD : ∀ n, HasGaussianLaw (fun w ↦ (Z n w,D n w)) (μ n))
    (hc : ∀ n (L : StrongDual ℝ (EuclideanSpace ℝ (Fin N))),
      cov[Z n, L ∘ D n; μ n] = L (c n) * Var[Z n; μ n])
    (a u : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (hv : ∀ n, 0 < v n) (hZ : ∀ n, HasLaw (Z n) (gaussianReal (a n) (v n)) (μ n))
    (hu : ∀ n, 0 ≤ u n)
    (hScale : Tendsto (fun n ↦ u n / Real.sqrt (v n:ℝ)) atTop (𝓝 1))
    (hOffset : ∀ x ∈ Ioi (0:ℝ), Tendsto (fun n ↦ (x-a n)/Real.sqrt (v n:ℝ)) atTop (𝓝 0))
    (W : H →ₗ[ℝ] (Ω' → ℝ)) (hmW : ∀ x, Measurable (W x))
    (hW : ∀ x, HasLaw (W x) (gaussianReal 0 (isoVar 1 x)) ν)
    {k : ℝ≥0} (hk : 0 < k) (f : Fin N → H) (hf : Function.Injective f)
    (hBaseVar : Tendsto (fun n ↦ Var[Z n; μ n]) atTop atTop)
    (A : ℝ) (hBaseMean : ∀ᶠ n in atTop, |∫ w, Z n w ∂(μ n)| ≤ A)
    (hBaseCov : ∀ L : StrongDual ℝ (EuclideanSpace ℝ (Fin N)),
      ∃ R : ℝ, ∀ᶠ n in atTop, |cov[Z n,L ∘ D n; μ n]| ≤ R)
    (hm : ∀ L : EuclideanSpace ℝ (Fin N), Tendsto (fun n ↦ ∫ w, ⟪L,D n w⟫ ∂(μ n)) atTop
      (𝓝 (∫ w, ⟪L,isoEuclidScores W k (fun i ↦ f i-f j) w⟫ ∂ν)))
    (hVar : ∀ L : EuclideanSpace ℝ (Fin N), Tendsto (fun n ↦ Var[fun w ↦ ⟪L,D n w⟫; μ n]) atTop
      (𝓝 (Var[fun w ↦ ⟪L,isoEuclidScores W k (fun i ↦ f i-f j) w⟫; ν]))) :
    Tendsto (fun n ↦ u n * winnerFaceWeight (μ n) (Z n) (D n)
      (WithLp.ofLp ⁻¹' winnerDifferenceFace j))
      atTop (𝓝 (φ 0 * (ν.map (fun w i ↦ isoScore W k (f i-f j) w)).real (winnerDifferenceFace j))) := by
  classical
  let Y : Ω' → EuclideanSpace ℝ (Fin N) := isoEuclidScores W k (fun i ↦ f i-f j)
  let J : Finset (Fin N) := Finset.univ.erase j
  let L (i : Fin N) := EuclideanSpace.proj (𝕜:=ℝ) i
  let b (_ : Fin N) : ℝ := 0
  let s (i : Fin N) : Bool := decide (i < j)
  have hNull : ∀ i ∈ J, (ν.map Y) (L i ⁻¹' {b i}) = 0 := by
    intro i hi
    have hij : i ≠ j := (Finset.mem_erase.mp hi).1
    exact isoEuclidScores_winner_null_face ν W hW hk f i j (fun h ↦ hij (hf h))
  have H := gaussian_winner_raw_thinLayer_tendsto_twoSpaces μ ν Z D c hmZ hmD hZD hc a u v hv hZ hu
    hScale hOffset Y (isoEuclidScores_hasGaussianLaw ν W hW k _) hBaseVar A hBaseMean hBaseCov hm hVar
    J (fun i ↦ L i) b s (fun i _ ↦ (L i).continuous) hNull
  let F : Set (EuclideanSpace ℝ (Fin N)) := {z | ∀ i ∈ J,
    z ∈ L i ⁻¹' (if s i then Iio (b i) else Iic (b i))}
  have hF : F = WithLp.ofLp ⁻¹' winnerDifferenceFace j := by
    ext z
    change (∀ i ∈ J, L i z ∈ (if s i then Iio (b i) else Iic (b i))) ↔
      (∀ i, i ≠ j → if i < j then (WithLp.ofLp z) i < 0 else (WithLp.ofLp z) i ≤ 0)
    constructor
    · intro hz i hi
      have hi' : i ∈ J := Finset.mem_erase.mpr ⟨hi,Finset.mem_univ _⟩
      have hh := hz i hi'
      by_cases h : i < j <;> simpa [L,b,s,h] using hh
    · intro hz i hi
      have hi' : i ≠ j := (Finset.mem_erase.mp hi).1
      have hh := hz i hi'
      by_cases h : i < j <;> simpa [L,b,s,h] using hh
  have hvect : Measurable (fun w i ↦ isoScore W k (f i-f j) w) :=
    Measurable.of_eval fun i ↦ (measurable_const.mul (hmW (f i-f j))).sub_const _
  have hmY : Measurable Y := (WithLp.measurable_toLp 2 (Fin N → ℝ)).comp hvect
  have hMap : (ν.map Y) F = (ν.map (fun w i ↦ isoScore W k (f i-f j) w)) (winnerDifferenceFace j) := by
    rw [hF,Measure.map_apply hmY ((WithLp.measurable_ofLp 2 (Fin N → ℝ))
        (measurableSet_winnerDifferenceFace j)),Measure.map_apply hvect (measurableSet_winnerDifferenceFace j)]
    rfl
  change Tendsto (fun n ↦ u n * winnerFaceWeight (μ n) (Z n) (D n) F)
    atTop (𝓝 (φ 0 * ((ν.map Y) F).toReal)) at H
  rwa [hMap,hF] at H

end CubeBrownian
#print axioms CubeBrownian.finiteGaussianWinner_coordinate_tendsto
