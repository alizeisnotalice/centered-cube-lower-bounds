import PairVarianceStability
import BoundedPair
import PairKernelDecay

open MeasureTheory ProbabilityTheory Set Filter CubeBrownian
open scoped NNReal ENNReal Topology ProbabilityTheory
namespace CubeSqrtPair

/-- A uniform finite-dimensional form of the first probabilistic part of
paperallpairs. All moments here are those of the actual perturbed densities. -/
theorem actual_pair_uniform_prefactor
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (d e : Ω → ℝ) (hmd : Measurable d) (hme : Measurable e)
    (a : ℝ) (ha0 : 0 ≤ a) (ha : a ≤ 1/8)
    (hd : ∀ w, |d w| ≤ a) (he : ∀ w, |e w| ≤ a)
    (hd0 : ∫ w, d w ∂P = 0) (he0 : ∫ w, e w ∂P = 0)
    {n : ℕ} (hn : 0 < n) (h u : ℝ) (hu : 0 < u)
    (hqY : u^2/2 ≤ (n:ℝ)*(∫ w, (d w)^2 ∂P))
    (hqZ : u^2/2 ≤ (n:ℝ)*(∫ w, (e w)^2 ∂P))
    (hCov : -Real.sqrt (∫ w, (d w)^2 ∂P) * Real.sqrt (∫ w, (e w)^2 ∂P)/2 ≤ cov[d,e;P]) :
    let L := fun w ↦ Real.log (1+d w)
    let J := fun w ↦ Real.log (1+e w)
    let H := avgAffinity P L J
    let A : Set (Fin n → Ω) := {x | h < ∑ i, L (x i)}
    let B : Set (Fin n → Ω) := {x | h < ∑ i, J (x i)}
    u*Real.exp h*(Measure.pi (fun _ : Fin n ↦ P)).real (A∩B) ≤
      (12*(φ 0+30))*H^n := by
  dsimp only
  let L := fun w ↦ Real.log (1+d w)
  let J := fun w ↦ Real.log (1+e w)
  let H := avgAffinity P L J
  let T := linearPair d e
  let V := logPair d e
  let Q := P.tilted V
  let v := Var[V;Q]
  let s := Real.sqrt (n:ℝ)*Real.sqrt v
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  have ha' : a ≤ 1/2 := ha.trans (by norm_num)
  have h2d : MemLp d 2 P := MemLp.of_bound hmd.aestronglyMeasurable a
    (Eventually.of_forall fun w ↦ by simpa only [Real.norm_eq_abs] using hd w)
  have h2e : MemLp e 2 P := MemLp.of_bound hme.aestronglyMeasurable a
    (Eventually.of_forall fun w ↦ by simpa only [Real.norm_eq_abs] using he w)
  have hLin := linear_pair_variance_lower P d e h2d h2e hd0 he0 hCov
  have hVarT : (u/3)^2 ≤ (n:ℝ)*Var[T;P] := by
    have h := mul_le_mul_of_nonneg_left hLin hnR.le
    change (n:ℝ)*((∫ w, (d w)^2 ∂P)+(∫ w, (e w)^2 ∂P)) ≤
      (n:ℝ)*(8*Var[T;P]) at h
    nlinarith only [h,hqY,hqZ,sq_nonneg u]
  have hTS : u/3 ≤ Real.sqrt (n:ℝ)*Real.sqrt (Var[T;P]) := by
    have hh := Real.sqrt_le_sqrt hVarT
    rw [Real.sqrt_sq (by positivity : 0 ≤ u/3),Real.sqrt_mul hnR.le] at hh
    exact hh
  have hS := (actual_logPair_sqrt_variance_sandwich P d e hmd hme a ha0 ha' hd he hLin).1
  have hRatio : (1/2:ℝ) ≤ Real.sqrt ((1-a)/(1+a)) := by
    have hh : (1/2:ℝ)^2 ≤ (1-a)/(1+a) := by
      apply (le_div_iff₀ (by positivity : 0 < 1+a)).2
      nlinarith only [ha]
    simpa only [Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 1/2)] using Real.sqrt_le_sqrt hh
  have hAmp : (1/2:ℝ) ≤ 1-4*a := by linarith only [ha]
  have hLS : Real.sqrt (Var[T;P])/4 ≤ Real.sqrt v := by
    have hNonneg := Real.sqrt_nonneg (Var[T;P])
    have hm := mul_le_mul hRatio hAmp (by norm_num : (0:ℝ)≤1/2) (Real.sqrt_nonneg _)
    have hh := mul_le_mul_of_nonneg_right hm hNonneg
    change Real.sqrt ((1-a)/(1+a))*((1-4*a)*Real.sqrt (Var[T;P])) ≤ Real.sqrt v at hS
    rw [mul_assoc] at hh
    nlinarith only [hh,hS]
  have hSL : u/12 ≤ s := by
    have hh := mul_le_mul_of_nonneg_left hLS (Real.sqrt_nonneg (n:ℝ))
    change u/12 ≤ Real.sqrt (n:ℝ)*Real.sqrt v
    nlinarith only [hh,hTS]
  have hs : 0 < s := (by positivity : 0 < u/12).trans_le hSL
  have hv : 0 < v := by
    apply Real.sqrt_pos.1
    by_contra! h
    have h' : s ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (Real.sqrt_nonneg _) h
    exact (not_le_of_gt hs) h'
  have hI := (logPair_density_ratio_bounds P d e hmd hme a ha' hd he).1
  have hB := paper_pair_bounded P L J (Real.measurable_log.comp (hmd.const_add _))
    (Real.measurable_log.comp (hme.const_add _)) hI (2*a) (by positivity)
    (logPair_abs_le_two_mul_amp d e a ha' hd he) hn h v hv rfl
  have hH : 0 ≤ H := integral_nonneg (fun _ ↦ (Real.exp_pos _).le)
  have hPhi : 0 ≤ φ 0 := gaussianPDFReal_nonneg _ _ _
  have hPF : u*((φ 0+120*(2*a))/s) ≤ 12*(φ 0+30) := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hs).2
    calc
      _ ≤ u*(φ 0+30) := mul_le_mul_of_nonneg_left (by linarith only [ha]) hu.le
      _ ≤ (12*s)*(φ 0+30) := mul_le_mul_of_nonneg_right (by linarith only [hSL]) (by linarith only [hPhi])
      _ = _ := by ring
  calc
    _ ≤ u*(H^n*((φ 0+120*(2*a))/s)) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hB hu.le
    _ = H^n*(u*((φ 0+120*(2*a))/s)) := by ring
    _ ≤ _ := by rw [mul_comm (12*(φ 0+30))]; exact mul_le_mul_of_nonneg_left hPF (pow_nonneg hH _)

end CubeSqrtPair
#print axioms CubeSqrtPair.actual_pair_uniform_prefactor
