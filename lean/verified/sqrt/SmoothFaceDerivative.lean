import SmoothFaceCutoff
import SmoothTransitionBounds
import SmoothProductBounds

open Set
open scoped BigOperators Pointwise

namespace CubeSqrtProbability

theorem iteratedDeriv_affine_real (f : ℝ → ℝ) (m : ℕ) (hf : ContDiff ℝ m f)
    (a b t : ℝ) :
    iteratedDeriv m (fun w ↦ f (a+b*w)) t = b^m * iteratedDeriv m f (a+b*t) := by
  have hs : (a +ᵥ (univ : Set ℝ)) = univ := by
    ext x
    constructor
    · intro _
      simp
    · intro _
      refine ⟨x-a,Set.mem_univ _,?_⟩
      change a+(x-a)=x
      ring
  have hshift : iteratedDeriv m (fun w ↦ f (a+w)) = fun x ↦ iteratedDeriv m f (a+x) := by
    simpa only [hs, iteratedDerivWithin_univ] using
      (iteratedDerivWithin_comp_const_add (f := f) (s := (univ : Set ℝ)) (n := m) a)
  have ha : ContDiff ℝ m (fun w ↦ f (a+w)) := hf.comp (contDiff_const.add contDiff_id)
  rw [iteratedDeriv_comp_const_mul ha b, hshift]

theorem exists_uniform_smoothTransition_derivative_const :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ m : ℕ, m ≤ 3 → ∀ x : ℝ, |iteratedDeriv m Real.smoothTransition x| ≤ C := by
  obtain ⟨C₁,_,h₁⟩ := exists_bound_iteratedDeriv_smoothTransition 1 (by decide)
  obtain ⟨C₂,_,h₂⟩ := exists_bound_iteratedDeriv_smoothTransition 2 (by decide)
  obtain ⟨C₃,_,h₃⟩ := exists_bound_iteratedDeriv_smoothTransition 3 (by decide)
  let C := max 1 (max C₁ (max C₂ C₃))
  refine ⟨C, le_max_left _ _, ?_⟩
  intro m hm x
  interval_cases m
  · rw [iteratedDeriv_zero,abs_of_nonneg (Real.smoothTransition.nonneg _)]
    exact (Real.smoothTransition.le_one _).trans (le_max_left _ _)
  · exact (h₁ x).trans ((le_max_left _ _).trans (le_max_right _ _))
  · exact (h₂ x).trans ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  · exact (h₃ x).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))

/-- Fixed-face smooth cutoffs have third directional derivatives bounded by a
threshold-independent constant times `(R/η)^3`. -/
theorem exists_smoothFace_directional_third_bound {ι : Type*} [Fintype ι] :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (c a d : ι → ℝ) (t η R : ℝ),
      0 < η → 0 ≤ R → (∀ i, |d i| ≤ R) → ∀ s : ℝ,
      |iteratedDeriv 3 (fun w ↦ smoothFaceCutoff c t η (fun i ↦ a i+w*d i)) s| ≤
        K * (R/η)^3 := by
  classical
  obtain ⟨C,hC,hCb⟩ := exists_uniform_smoothTransition_derivative_const
  refine ⟨(8*C)^(Fintype.card ι), pow_nonneg (by linarith) _, ?_⟩
  intro c a d t η R hη hR hd s
  let A (i : ι) := (c i+t+η-a i)/η
  let B (i : ι) := -(d i/η)
  let f (i : ι) (w : ℝ) := Real.smoothTransition (A i+B i*w)
  have hprod : (fun w ↦ smoothFaceCutoff c t η (fun i ↦ a i+w*d i)) =
      (fun w ↦ ∏ i ∈ Finset.univ, f i w) := by
    funext w
    unfold smoothFaceCutoff
    apply Finset.prod_congr rfl
    intro i _
    unfold f A B
    congr 1
    ring
  have hf (i : ι) : ContDiff ℝ 3 (f i) :=
    (Real.smoothTransition.contDiff (n := 3)).comp (by unfold A B; fun_prop)
  have hbound (i : ι) (m : ℕ) (hm : m ≤ 3) (w : ℝ) :
      |iteratedDeriv m (f i) w| ≤ C*(R/η)^m := by
    unfold f
    rw [iteratedDeriv_affine_real _ m Real.smoothTransition.contDiff, abs_mul, abs_pow]
    have hB : |B i| ≤ R/η := by
      unfold B
      rw [abs_neg,abs_div,abs_of_pos hη]
      exact div_le_div_of_nonneg_right (hd i) hη.le
    calc
      _ ≤ (R / η) ^ m * C :=
        mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hB _)
          (hCb m hm _) (abs_nonneg _) (pow_nonneg (div_nonneg hR hη.le) _)
      _ = _ := mul_comm _ _
  rw [hprod]
  simpa using smooth_finite_product_iteratedDeriv_bound (Finset.univ : Finset ι)
      f C (R/η) hC (div_nonneg hR hη.le) (fun i _ ↦ hf i) (fun i _ ↦ hbound i) 3 (le_refl _) s

end CubeSqrtProbability
#print axioms CubeSqrtProbability.exists_smoothFace_directional_third_bound
