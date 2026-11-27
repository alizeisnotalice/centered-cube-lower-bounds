import ProductTilt
import Mathlib.MeasureTheory.Measure.Tilted

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal ProbabilityTheory
namespace CubeSqrtPair

noncomputable def pairScore {Ω : Type*} (L J : Ω → ℝ) (w : Ω) : ℝ :=
  (L w+J w)/2

noncomputable def avgAffinity {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (L J : Ω → ℝ) : ℝ :=
  ∫ w, Real.exp (pairScore L J w) ∂P

theorem avgAffinity_eq_hellinger
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Y Z : Ω → ℝ)
    (hY : ∀ w, 0 < Y w) (hZ : ∀ w, 0 < Z w) :
    avgAffinity P (fun w ↦ Real.log (Y w)) (fun w ↦ Real.log (Z w)) =
      ∫ w, Real.sqrt (Y w*Z w) ∂P := by
  unfold avgAffinity
  apply integral_congr_ae
  exact Eventually.of_forall fun w ↦ by
    dsimp only [pairScore]
    rw [← Real.log_mul (hY w).ne' (hZ w).ne']
    rw [Real.sqrt_eq_rpow,Real.rpow_def_of_pos (mul_pos (hY w) (hZ w))]
    congr 1
    ring

/-- Exact affinity-preserving change of measure for the common average score. -/
theorem affinity_product_transfer
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (V : Ω → ℝ)
    (hm : Measurable V) (hInt : Integrable (fun w ↦ Real.exp (V w)) P)
    (n : ℕ) (h : ℝ) :
    let Q := P.tilted V
    let S (x : Fin n → Ω) := ∑ i, V (x i)
    let H := ∫ w, Real.exp (V w) ∂P
    Real.exp h * (Measure.pi (fun _ : Fin n ↦ P)).real {x | h < S x} =
      H^n * ∫ x in {x | h < S x}, Real.exp (-(S x-h)) ∂(Measure.pi (fun _ : Fin n ↦ Q)) := by
  dsimp only
  let Q := P.tilted V
  let S (x : Fin n → Ω) := ∑ i, V (x i)
  let H := ∫ w, Real.exp (V w) ∂P
  let Pπ := Measure.pi (fun _ : Fin n ↦ P)
  let E := {x | h < S x}
  have hmS : Measurable S := Finset.measurable_sum _ fun i _ ↦ hm.comp (measurable_pi_apply i)
  have hE : MeasurableSet E := measurableSet_lt measurable_const hmS
  have ht : Pπ.tilted S = Measure.pi (fun _ : Fin n ↦ Q) := by
    simpa only [S,Pπ,Q,one_mul] using
      CubeMD.tilted_pi_eq_pi_tilted (fun _ : Fin n ↦ P) (fun _ ↦ V) 1
        (fun _ ↦ by simpa only [one_mul] using hInt)
  have hH : 0 < H := by
    simpa only [H,mgf,one_mul] using
      (mgf_pos (μ:=P) (X:=V) (t:=1) (by simpa only [one_mul] using hInt))
  have hM : (∫ x, Real.exp (S x) ∂Pπ) = H^n := by
    simp only [Pπ,S,Real.exp_sum]
    rw [integral_fintype_prod_eq_prod (fun _ : Fin n ↦ fun w : Ω ↦ Real.exp (V w))]
    simp [H]
  change Real.exp h * Pπ.real E =
    H^n * ∫ x in E, Real.exp (-(S x-h)) ∂(Measure.pi (fun _ : Fin n ↦ Q))
  rw [← ht,setIntegral_tilted' S _ hE,hM]
  have hh (x : Fin n → Ω) : (Real.exp (S x) / H^n) • Real.exp (-(S x-h)) =
      Real.exp h/H^n := by
    rw [smul_eq_mul,div_mul_eq_mul_div,← Real.exp_add]
    congr 2
    ring
  simp_rw [hh]
  rw [setIntegral_const,smul_eq_mul]
  field_simp [hH.ne']

end CubeSqrtPair
#print axioms CubeSqrtPair.affinity_product_transfer
#print axioms CubeSqrtPair.avgAffinity_eq_hellinger
