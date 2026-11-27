import PaperMesh
import ActualFiniteSmoothing
import CanonicalBrownianContinuous

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace CubeBrownian
set_option maxHeartbeats 2200000

noncomputable def actualPaperKappa (L : ℝ) : ℝ≥0 :=
  Real.toNNReal (29/(9*L^2))

theorem actualPaperKappa_coe (L : ℝ) :
    (actualPaperKappa L:ℝ) = 29/(9*L^2) := by
  unfold actualPaperKappa
  exact Real.coe_toNNReal _ (by positivity)

theorem actualPaperKappa_range (L : ℝ) (hL : L ∈ Icc (10/9:ℝ) (11/9:ℝ)) :
    actualPaperKappa L ∈ Icc (261/121:ℝ≥0) (261/100:ℝ≥0) := by
  have hL0 : 0 < L := (by norm_num : (0:ℝ)<10/9).trans_le hL.1
  have hl : (10/9:ℝ)^2 ≤ L^2 := pow_le_pow_left₀ (by norm_num) hL.1 2
  have hu : L^2 ≤ (11/9:ℝ)^2 := pow_le_pow_left₀ hL0.le hL.2 2
  constructor
  · change ((261/121:ℝ≥0):ℝ) ≤ (actualPaperKappa L:ℝ)
    rw [actualPaperKappa_coe]
    push_cast
    exact (le_div_iff₀ (by positivity)).2 (by linarith)
  · change (actualPaperKappa L:ℝ) ≤ ((261/100:ℝ≥0):ℝ)
    rw [actualPaperKappa_coe]
    push_cast
    exact (div_le_iff₀ (by positivity)).2 (by linarith)

noncomputable def actualPaperGrid (T : ℕ) (i : Fin (T^3+1)) : ℝ≥0 :=
  cellLeft (1/((T:ℝ≥0)^2)) i

noncomputable def actualSmoothedGridMean (T w : ℕ) (L : ℝ) : ℝ :=
  let e : ℝ := 1/max (w:ℝ) 1
  canonicalFiniteGridExp
    (fun i => centeredBoxNodeL2 e (actualPaperGrid T i) (by positivity)
      (NNReal.coe_nonneg (actualPaperGrid T i)))
    (2*actualPaperKappa L)

/-- With any actual continuous Brownian process, the exact canonical finite
smoothed Gaussian scores obey the manuscript lower intensity uniformly on I.
The needed finite smoothing width can be chosen after T. -/
theorem actualSmoothedGridMean_eventually_lower
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B μ) (ε : ℝ) (he : 0<ε) :
    ∀ᶠ T : ℕ in atTop, 2≤T ∧
      ∀ᶠ w : ℕ in atTop, T^2+4≤w ∧ ∀ L ∈ Icc (10/9:ℝ) (11/9:ℝ),
        (T:ℝ)*(29/(9*L^2)-ε) ≤ actualSmoothedGridMean T w L := by
  have hmesh := paperMesh_uniform_expectation μ hB
    (lo := (261/121:ℝ≥0)) (hi := (261/100:ℝ≥0))
    (by norm_num) (by norm_num) (ε/2) (by positivity)
  have hD : Tendsto (fun w : ℕ => max (w:ℝ) 1) atTop atTop :=
    tendsto_atTop_mono (fun n : ℕ => le_max_left (n:ℝ) 1) tendsto_natCast_atTop_atTop
  have hE : Tendsto (fun w : ℕ => 1/max (w:ℝ) 1) atTop (𝓝 0) := by
    simpa only [one_div,Function.comp_def] using tendsto_inv_atTop_zero.comp hD
  filter_upwards [hmesh,eventually_ge_atTop (2:ℕ)] with T hT hn
  refine ⟨hn,?_⟩
  have hT0 : 0<(T:ℝ) := by exact_mod_cast (show 0<T by omega)
  have hsmooth := canonical_centeredBox_grid_uniform_Brownian μ B hB.toIsPreBrownianReal
    (actualPaperGrid T) (fun w : ℕ => 1/max (w:ℝ) 1) (fun _ => by positivity) hE
    (2*(261/100:ℝ≥0)) (T*ε/2) (by positivity)
  filter_upwards [hsmooth,eventually_ge_atTop (T^2+4)] with w hS hw
  refine ⟨hw,?_⟩
  intro L hL
  have hκ := actualPaperKappa_range L hL
  have hBnd : 2*actualPaperKappa L ≤ 2*(261/100:ℝ≥0) :=
    mul_le_mul_of_nonneg_left hκ.2 (by norm_num)
  have hg := hS (2*actualPaperKappa L) hBnd
  have hex :
      (∫ x, Real.exp (⨆ i : Fin (T^3+1),
        Real.sqrt ((2*actualPaperKappa L:ℝ≥0):ℝ) * B (actualPaperGrid T i) x -
          ((2*actualPaperKappa L:ℝ≥0):ℝ)*(actualPaperGrid T i:ℝ)/2) ∂μ) =
      ∫ x, Real.exp (paperMeshGridMax B (actualPaperKappa L) T x) ∂μ := by
    apply integral_congr_ae
    apply Eventually.of_forall
    intro x
    unfold paperMeshGridMax actualPaperGrid
    apply congrArg Real.exp
    apply congrArg iSup
    funext i
    push_cast
    ring
  rw [hex] at hg
  change |actualSmoothedGridMean T w L -
    (∫ x, Real.exp (paperMeshGridMax B (actualPaperKappa L) T x) ∂μ)| < (T:ℝ)*ε/2 at hg
  have hb := hT (actualPaperKappa L) hκ
  rw [actualPaperKappa_coe, abs_lt] at hb
  have hbr := (lt_div_iff₀ hT0).1 (by linarith only [hb.1] :
    29/(9*L^2)-ε/2 < (∫ x, Real.exp (paperMeshGridMax B (actualPaperKappa L) T x) ∂μ)/(T:ℝ))
  rw [abs_lt] at hg
  linarith only [hbr,hg.1]

theorem actualSmoothedGridMean_unconditional_lower (ε : ℝ) (he : 0<ε) :
    ∀ᶠ T : ℕ in atTop, 2≤T ∧
      ∀ᶠ w : ℕ in atTop, T^2+4≤w ∧ ∀ L ∈ Icc (10/9:ℝ) (11/9:ℝ),
        (T:ℝ)*(29/(9*L^2)-ε) ≤ actualSmoothedGridMean T w L :=
  actualSmoothedGridMean_eventually_lower paperWienerCylinder paperWienerBrownian_isBrownian ε he

#print axioms actualSmoothedGridMean_unconditional_lower

#print axioms actualSmoothedGridMean_eventually_lower
end CubeBrownian
