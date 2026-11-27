import AffinityTransfer
import IIDScalarBerry
import WeightedNormalTail
import FourthMomentThird
open MeasureTheory ProbabilityTheory Filter Set CubeBrownian
open scoped NNReal ENNReal Topology ProbabilityTheory
namespace CubeSqrtPair

theorem pair_bearing_error_bound (n v I M4 : ℝ) (hn : 0 < n) (hv : 0 < v)
    (hI : I ≤ Real.sqrt v*Real.sqrt M4) :
    30 * (n * (I/(Real.sqrt n * Real.sqrt v)^3)) ≤
      30 * Real.sqrt M4/(v * Real.sqrt n) := by
  let r := Real.sqrt n
  let t := Real.sqrt v
  have hr : 0 < r := Real.sqrt_pos.2 hn
  have ht : 0 < t := Real.sqrt_pos.2 hv
  have hr2 : r^2 = n := Real.sq_sqrt hn.le
  have ht2 : t^2 = v := Real.sq_sqrt hv.le
  let s := r*t
  have hs : 0 < s := mul_pos hr ht
  change 30*(n*(I/s^3)) ≤ 30*Real.sqrt M4/(v*r)
  calc
    _ ≤ 30*(n*((t*Real.sqrt M4)/s^3)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right hI (pow_nonneg hs.le _)) hn.le) (by norm_num)
    _ = _ := by
      dsimp [s]
      rw [mul_pow,show r^3 = n*r by rw [pow_succ,hr2],
        show t^3 = v*t by rw [pow_succ,ht2]]
      field_simp [hr.ne',ht.ne',hn.ne',hv.ne']

/-- Exact manuscript two-point bound: the full Berry–Esseen error is
multiplied by the original Hellinger affinity to the power n. -/
theorem paper_pair_actual
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (L J : Ω → ℝ)
    (hmL : Measurable L) (hmJ : Measurable J)
    (hInt : Integrable (fun w ↦ Real.exp (pairScore L J w)) P)
    (h2 : MemLp (pairScore L J) 2 (P.tilted (pairScore L J)))
    {n : ℕ} (hn : 0 < n) (h : ℝ)
    (v : ℝ) (hv : 0 < v)
    (hVar : Var[pairScore L J;P.tilted (pairScore L J)] = v)
    (h4 : Integrable (fun w ↦ (pairScore L J w-
      ∫ z, pairScore L J z ∂(P.tilted (pairScore L J)))^4) (P.tilted (pairScore L J))) :
    let V := pairScore L J
    let Q := P.tilted V
    let m := ∫ w, V w ∂Q
    let M := (n:ℝ)*m
    let m4 := ∫ w, (V w-m)^4 ∂Q
    let s := Real.sqrt (n:ℝ)*Real.sqrt v
    let ε := 30*Real.sqrt m4/(v*Real.sqrt (n:ℝ))
    let H := avgAffinity P L J
    let A : Set (Fin n → Ω) := {x | h < ∑ i, L (x i)}
    let B : Set (Fin n → Ω) := {x | h < ∑ i, J (x i)}
    Real.exp h*(Measure.pi (fun _ : Fin n ↦ P)).real (A∩B) ≤
      H^n*((∫ r in Ioi (0:ℝ), Real.exp (-r)*gaussianPDFReal (M-h)
        (NNReal.mk (s^2) (sq_nonneg _)) r)+2*ε)
    ∧ Real.exp h*(Measure.pi (fun _ : Fin n ↦ P)).real (A∩B) ≤ H^n*(φ 0/s+2*ε) := by
  dsimp only
  let V := pairScore L J
  let Q := P.tilted V
  let m := ∫ w, V w ∂Q
  let M := (n:ℝ)*m
  let m4 := ∫ w, (V w-m)^4 ∂Q
  let s := Real.sqrt (n:ℝ)*Real.sqrt v
  let ε := 30*Real.sqrt m4/(v*Real.sqrt (n:ℝ))
  let H := avgAffinity P L J
  let Pπ := Measure.pi (fun _ : Fin n ↦ P)
  let Qπ := Measure.pi (fun _ : Fin n ↦ Q)
  let S (x : Fin n → Ω) := ∑ i, V (x i)
  let A : Set (Fin n → Ω) := {x | h < ∑ i, L (x i)}
  let B : Set (Fin n → Ω) := {x | h < ∑ i, J (x i)}
  let W : Set (Fin n → Ω) := {x | h < S x}
  let vN : ℝ≥0 := ⟨s^2,sq_nonneg _⟩
  let D := ∫ r in Ioi (0:ℝ), Real.exp (-r)*gaussianPDFReal (M-h) vN r
  have hmV : Measurable V := (hmL.add hmJ).div_const 2
  have hmS : Measurable S := Finset.measurable_sum _ (fun i _ ↦ hmV.comp (measurable_pi_apply i))
  let _ : IsProbabilityMeasure Q := isProbabilityMeasure_tilted hInt
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  have hs : 0 < s := mul_pos (Real.sqrt_pos.2 hnR) (Real.sqrt_pos.2 hv)
  have hM4 := centered_third_le_sd_fourth Q V hmV h2 m rfl h4
  have hErr : 30 * ((n:ℝ)*((∫ w, |V w-m|^3 ∂Q)/s^3)) ≤ ε := by
    apply pair_bearing_error_bound _ _ _ _ hnR hv
    have hVQ : Var[V;Q] = v := hVar
    simpa only [hVQ,m4] using hM4.2
  have hCDF (a : ℝ) : |(Qπ.map (fun x ↦ (S x-M)/s)).real (Iic a) -
      (gaussianReal 0 1).real (Iic a)| ≤ ε :=
    (iid_scalar_berry_cdf Q V hmV h2 m rfl v hv hVar hM4.1 hn a).trans hErr
  have hWT : (∫ x in W, Real.exp (-(S x-h)) ∂Qπ) ≤ D+2*ε :=
    weighted_tail_normal_comparison Qπ S hmS M s h ε hs hCDF
  have hTrans : Real.exp h * Pπ.real W =
      H^n * ∫ x in W, Real.exp (-(S x-h)) ∂Qπ :=
    affinity_product_transfer P V hmV hInt n h
  have hSub : A∩B ⊆ W := by
    intro x hx
    have hS : S x = ((∑ i, L (x i)) + ∑ i, J (x i))/2 := by
      simp only [S,V,pairScore,← Finset.sum_div,Finset.sum_add_distrib]
    have hA : h < ∑ i, L (x i) := hx.1
    have hB : h < ∑ i, J (x i) := hx.2
    change h < S x
    rw [hS]
    linarith only [hA,hB]
  have hH : 0 ≤ H := integral_nonneg (fun _ ↦ (Real.exp_pos _).le)
  have hFirst : Real.exp h * Pπ.real (A∩B) ≤ H^n*(D+2*ε) :=
    (mul_le_mul_of_nonneg_left (measureReal_mono hSub) (Real.exp_pos _).le).trans
      (hTrans.le.trans (mul_le_mul_of_nonneg_left hWT (pow_nonneg hH _)))
  have hPeak : D ≤ φ 0/s := by
    have hp : 0 < vN := by change 0 < s^2; exact sq_pos_of_pos hs
    have hh := gaussian_density_weighted_le_peak (M-h) vN hp
    change D ≤ φ 0/Real.sqrt (s^2) at hh
    simpa only [Real.sqrt_sq hs.le] using hh
  exact ⟨hFirst,hFirst.trans (mul_le_mul_of_nonneg_left (add_le_add_left hPeak _) (pow_nonneg hH _))⟩

end CubeSqrtPair
#print axioms CubeSqrtPair.paper_pair_actual
