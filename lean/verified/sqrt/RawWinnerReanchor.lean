import TrueTiltPolarization

open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace CubeSqrtProbability

variable {Ω : Type*} [MeasurableSpace Ω]
variable (P : Measure Ω) [IsProbabilityMeasure P]

/-- Change the raw cross-moment's anchor from the packet's left endpoint X
to its actual winner Y; the difference is an exact polarized distance. -/
theorem raw_reanchor_cross_exact (X Y Z : Ω → ℝ)
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    {a : ℝ} (ha : 0≤a)
    (hx : ∀ w, |X w|≤a) (hy : ∀ w, |Y w|≤a) (hz : ∀ w, |Z w|≤a) :
    (∫ w, Y w*(Z w-Y w) ∂P) = (∫ w, X w*(Z w-Y w) ∂P) -
      rawIncCross P Y X Z := by
  have hi (U : Ω → ℝ) (hU : Measurable U) (hu : ∀ w, |U w|≤a) :
      Integrable (fun w ↦ U w*(Z w-Y w)) P := by
    apply integrable_of_uniform_abs P (hU.mul (hZ.sub hY)) (B := a*(2*a))
    intro w
    rw [Pi.mul_apply,Pi.sub_apply,abs_mul]
    exact mul_le_mul (hu w) (abs_sub_of_common_bound (hy w) (hz w)) (abs_nonneg _) ha
  unfold rawIncCross
  have hh := integral_sub (hi X hX hx) (hi Y hY hy)
  have e : (fun w ↦ (X w-Y w)*(Z w-Y w)) =
      fun w ↦ X w*(Z w-Y w)-Y w*(Z w-Y w) := by funext w; ring
  rw [e,hh]
  ring

/-- Baseline quadratic energy changes by only the deterministic
baseline-increment product and the raw squared distance. -/
theorem raw_reanchor_variance_exact (X Y : Ω → ℝ)
    (hX : Measurable X) (hY : Measurable Y)
    {a : ℝ} (ha : 0≤a) (hx : ∀ w, |X w|≤a) (hy : ∀ w, |Y w|≤a) :
    rawSq P Y-rawSq P X =
      2*(∫ w, X w*(Y w-X w) ∂P)+rawSq P (fun w ↦ Y w-X w) := by
  have hY2 : Integrable (fun w ↦ (Y w)^2) P := by
    apply integrable_of_uniform_abs P (hY.pow_const 2) (B:=a^2)
    intro w
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hy w) _
  have hX2 : Integrable (fun w ↦ (X w)^2) P := by
    apply integrable_of_uniform_abs P (hX.pow_const 2) (B:=a^2)
    intro w
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hx w) _
  have hsub (w : Ω) : |Y w-X w|≤2*a := abs_sub_of_common_bound (hx w) (hy w)
  have hDist : Integrable (fun w ↦ (Y w-X w)^2) P := by
    apply integrable_of_uniform_abs P ((hY.sub hX).pow_const 2) (B:=(2*a)^2)
    intro w
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hsub w) _
  have hInc : Integrable (fun w ↦ X w*(Y w-X w)) P := by
    apply integrable_of_uniform_abs P (hX.mul (hY.sub hX)) (B:=a*(2*a))
    intro w
    rw [Pi.mul_apply,Pi.sub_apply,abs_mul]
    exact mul_le_mul (hx w) (hsub w) (abs_nonneg _) ha
  unfold rawSq
  rw [← integral_sub hY2 hX2, ← integral_const_mul]
  have hSum := integral_add (hInc.const_mul 2) hDist
  rw [← hSum]
  congr 1
  funext w
  ring

end CubeSqrtProbability
#print axioms CubeSqrtProbability.raw_reanchor_cross_exact
#print axioms CubeSqrtProbability.raw_reanchor_variance_exact
