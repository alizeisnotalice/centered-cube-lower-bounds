import SqrtSpectralMixedGram

namespace CenteredCubeSqrt
open MeasureTheory Set
open scoped Interval BigOperators
set_option maxHeartbeats 1400000

theorem real_spectralCoeff_nat_majorant {m : ℕ} (hm : 0<m) :
    plateauSpectralCoeff m≤(144/29)/((m:ℝ)^4) := by
  have hm' : 0<(m:ℝ) := by exact_mod_cast hm
  have h := plateauSumTerm_majorant (1/(2*(m:ℝ))) hm
  have e : Real.pi*(m:ℝ)*(1/(2*(m:ℝ)))=Real.pi/2 := by field_simp
  rw [plateauSumTerm,e,Real.sin_pi_div_two,one_pow,mul_one] at h
  exact h

theorem spectralMixedTerm_abs_le_coeff (L J : ℝ) (m : ℕ) :
    |spectralMixedTerm L J m|≤plateauSpectralCoeff m := by
  unfold spectralMixedTerm
  rw [abs_mul,abs_mul,abs_of_nonneg (plateauSpectralCoeff_nonneg _)]
  calc
    _ ≤ plateauSpectralCoeff m*|Real.sin (Real.pi*(m:ℝ)*L)| :=
      mul_le_of_le_one_right (mul_nonneg (plateauSpectralCoeff_nonneg _) (abs_nonneg _)) (Real.abs_sin_le_one _)
    _ ≤ _ := mul_le_of_le_one_right (plateauSpectralCoeff_nonneg _) (Real.abs_sin_le_one _)

theorem actualLowSpectrum_cross_lower {L J : ℝ} (hL : L∈Icc (10/9:ℝ) (11/9))
    (hJ : J∈Icc (10/9:ℝ) (11/9)) (M : ℕ) :
    -(1/116:ℝ) ≤ periodInner (actualLowSpectrum M L) (actualLowSpectrum M J) := by
  rw [actualLowSpectrum_inner_eq]
  rcases le_total M 4 with hM | hM
  · have h : 0 ≤ ∑ k ∈ Finset.range M,spectralMixedTerm L J (k+1) := by
      refine Finset.sum_nonneg (fun k hk => shifted_harmonic_product_nonneg hL hJ ?_)
      have := Finset.mem_range.mp hk
      omega
    linarith
  · obtain ⟨r,hr⟩ := Nat.exists_eq_add_of_le hM
    rw [hr,Finset.sum_range_add]
    have lo : 0 ≤ ∑ k ∈ Finset.range 4,spectralMixedTerm L J (k+1) := by
      refine Finset.sum_nonneg (fun k hk => shifted_harmonic_product_nonneg hL hJ ?_)
      have := Finset.mem_range.mp hk
      omega
    let f (j : ℕ) := 1/((4:ℝ)+(j:ℝ)+1)^4
    have hs : Summable f := by
      have h := ((summable_nat_add_iff 5).2 ((Real.summable_nat_pow_inv (p:=4)).2 (by decide)))
      convert h using 1
      funext j
      unfold f
      push_cast
      have e : (4:ℝ)+(j:ℝ)+1=(j:ℝ)+5 := by ring
      rw [e,one_div]
    have ht : (∑ k ∈ Finset.range r,f k)≤1/(3*(4:ℝ)^3) :=
      (hs.sum_le_tsum _ (fun _ _ => by unfold f; positivity)).trans (inverseFourth_tail 4 (by decide))
    have hm (k : ℕ) : -(144/29)*f k≤spectralMixedTerm L J (4+k+1) := by
      have h := (spectralMixedTerm_abs_le_coeff L J (4+k+1)).trans
        (real_spectralCoeff_nat_majorant (m:=4+k+1) (by omega))
      have h' := (abs_le.mp h).1
      simp only [Nat.cast_add,Nat.cast_one,Nat.cast_ofNat] at h'
      unfold f
      convert h' using 1
      ring
    have H := Finset.sum_le_sum (fun k (_ : k∈Finset.range r) => hm k)
    rw [←Finset.mul_sum] at H
    have HH := mul_le_mul_of_nonneg_left ht (show (0:ℝ)≤144/29 by norm_num)
    norm_num at HH
    linarith

#print axioms actualLowSpectrum_cross_lower

end CenteredCubeSqrt
