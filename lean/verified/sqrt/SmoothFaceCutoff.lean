import PolyhedralSandwich
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

open Set
open scoped BigOperators

namespace CubeSqrtProbability

/-- At each projected coordinate the transition takes place on the interval
between its current threshold and its expansion by `η`. -/
noncomputable def smoothFaceCutoff {ι : Type*} [Fintype ι]
    (c : ι → ℝ) (t η : ℝ) (x : ι → ℝ) : ℝ :=
  ∏ i, Real.smoothTransition ((c i+t+η-x i)/η)

theorem smoothFaceCutoff_contDiff {ι : Type*} [Fintype ι]
    (c : ι → ℝ) (t η : ℝ) :
    ContDiff ℝ 3 (smoothFaceCutoff c t η) := by
  classical
  unfold smoothFaceCutoff
  have hA (i : ι) : ContDiff ℝ 3 (fun x : ι → ℝ ↦ (c i+t+η-x i)/η) := by
    exact (contDiff_const.sub (contDiff_apply ℝ (fun _ : ι ↦ ℝ) i)).div_const η
  have hB (s : Finset ι) :
      ContDiff ℝ 3 (fun x : ι → ℝ ↦
        ∏ i ∈ s, Real.smoothTransition ((c i+t+η-x i)/η)) := by
    induction s using Finset.induction_on with
    | empty => simpa using (contDiff_const : ContDiff ℝ 3 (fun _ : ι → ℝ ↦ (1:ℝ)))
    | insert i s hi hs =>
      simp only [Finset.prod_insert hi]
      exact ((Real.smoothTransition.contDiff (n := 3)).comp (hA i)).mul hs
  exact hB Finset.univ

theorem smoothFaceCutoff_nonneg {ι : Type*} [Fintype ι]
    (c : ι → ℝ) (t η : ℝ) (x : ι → ℝ) : 0 ≤ smoothFaceCutoff c t η x :=
  Finset.prod_nonneg (fun _ _ ↦ Real.smoothTransition.nonneg _)

theorem smoothFaceCutoff_le_one {ι : Type*} [Fintype ι]
    (c : ι → ℝ) (t η : ℝ) (x : ι → ℝ) : smoothFaceCutoff c t η x ≤ 1 :=
  Finset.prod_le_one₀ (fun _ _ ↦ Real.smoothTransition.nonneg _)
    (fun _ _ ↦ Real.smoothTransition.le_one _)

theorem smoothFaceCutoff_eq_one_of_mem {ι : Type*} [Fintype ι]
    (strict : ι → Bool) (c : ι → ℝ) (t : ℝ) {η : ℝ} (hη : 0 < η)
    {x : ι → ℝ} (hx : x ∈ faceEvent id strict c t) : smoothFaceCutoff c t η x = 1 := by
  unfold smoothFaceCutoff
  apply Finset.prod_eq_one
  intro i _
  have hi := hx i
  have hx' : x i ≤ c i+t := by
    cases hs : strict i
    · simpa [facePass,hs] using hi
    · exact le_of_lt (by simpa [facePass,hs] using hi)
  apply Real.smoothTransition.one_of_one_le
  exact (le_div_iff₀ hη).mpr (by linarith)

theorem smoothFaceCutoff_eq_zero_of_not_mem {ι : Type*} [Fintype ι]
    (strict : ι → Bool) (c : ι → ℝ) (t : ℝ) {η : ℝ} (hη : 0 < η)
    {x : ι → ℝ} (hx : x ∉ faceEvent id strict c (t+η)) : smoothFaceCutoff c t η x = 0 := by
  classical
  change ¬ ∀ i, facePass (strict i) (x i) (c i+(t+η)) at hx
  obtain ⟨i, hi⟩ := not_forall.mp hx
  have hx' : c i+t+η ≤ x i := by
    cases hs : strict i
    · have hh : c i+(t+η) < x i := by simpa [facePass,hs] using hi
      linarith
    · have hh : c i+(t+η) ≤ x i := by simpa [facePass,hs] using hi
      linarith
  unfold smoothFaceCutoff
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  exact Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hη.le)

end CubeSqrtProbability
#print axioms CubeSqrtProbability.smoothFaceCutoff_contDiff
#print axioms CubeSqrtProbability.smoothFaceCutoff_eq_one_of_mem
#print axioms CubeSqrtProbability.smoothFaceCutoff_eq_zero_of_not_mem
