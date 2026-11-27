import Mathlib

namespace CubeMD

noncomputable def singleThreshold (u v : ℝ) : ℝ := (u^2+v^2)/(2*v)

theorem singleThreshold_displacement (u v : ℝ) (hv : 0 < v) :
    singleThreshold u v - u = (v-u)^2/(2*v) := by
  unfold singleThreshold
  field_simp [hv.ne'] <;> ring

/-- A fixed small absolute perturbation of the physical scale suffices for
the paper's squared threshold window. -/
theorem singleThreshold_stable (u v : ℝ) (hu : 1 ≤ u) (h : |v-u| ≤ 1/8) :
    let z := singleThreshold u v
    0 < v ∧ u ≤ z ∧ z ≤ 2*u ∧ z^2-u^2 ≤ 1 := by
  dsimp only
  have hu' : 0 < u := by linarith
  have hv : 0 < v := by linarith [(abs_le.mp h).1]
  have hvh : u ≤ 2*v := by linarith [(abs_le.mp h).1]
  have he := singleThreshold_displacement u v hv
  have hδ : 0 ≤ singleThreshold u v - u := by rw [he]; positivity
  have hs : (v-u)^2 ≤ (1/8 : ℝ)^2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h _
  have hm : u*(singleThreshold u v-u) ≤ 1/64 := by
    rw [he, ← mul_div_assoc]
    apply (div_le_iff₀ (by positivity : 0 < 2*v)).2
    have hh := mul_le_mul_of_nonneg_left hs hu'.le
    nlinarith only [hh,hvh]
  have hzz : singleThreshold u v ≤ 2*u := by
    have hh := mul_le_mul_of_nonneg_right hu hδ
    linarith only [hh,hm,hu]
  have hd := mul_le_mul_of_nonneg_left (show singleThreshold u v + u ≤ 3*u by linarith only [hzz]) hδ
  exact ⟨hv, by linarith only [hδ], hzz, by nlinarith only [hd,hm]⟩

/-- Translate the variance and radius ratios in the paper into scale
stability, allowing slack in the large-K assumption. -/
theorem scale_displacement_of_ratios (u K ρ V : ℝ)
    (hu : 1 ≤ u) (hK : 32*u ≤ K)
    (hρ : |ρ-1| ≤ 1/(75*u))
    (hV : |V-1| ≤ 2/K) :
    |u*(Real.sqrt V/ρ)-u| ≤ 1/8 := by
  have hu' : 0 < u := by linarith
  have hK' : 0 < K := by linarith
  have ha : (1:ℝ)/(75*u) ≤ 1/75 := by
    apply (div_le_iff₀ (by positivity : 0 < 75*u)).mpr
    linarith
  have hb : (2:ℝ)/K ≤ 1/16 := by
    apply (div_le_iff₀ hK').mpr
    linarith
  have hρ' : 0 < ρ := by linarith [(abs_le.mp (hρ.trans ha)).1]
  have hρlo : 74/75 ≤ ρ := by linarith [(abs_le.mp (hρ.trans ha)).1]
  have hV0 : 0 ≤ V := by linarith [(abs_le.mp (hV.trans hb)).1]
  have hsV : |Real.sqrt V-1| ≤ |V-1| := by
    have he : |V-1| = |Real.sqrt V-1| *(Real.sqrt V+1) := by
      rw [show V-1 = (Real.sqrt V-1)*(Real.sqrt V+1) by nlinarith [Real.sq_sqrt hV0],
        abs_mul,abs_of_nonneg (by positivity : 0 ≤ Real.sqrt V+1)]
    rw [he]
    nlinarith [abs_nonneg (Real.sqrt V-1), Real.sqrt_nonneg V]
  have htri : |Real.sqrt V-ρ| ≤ 2/K + 1/(75*u) := calc
    _ ≤ |Real.sqrt V-1| + |ρ-1| := by
      apply abs_le.mpr
      constructor <;> linarith [neg_abs_le (Real.sqrt V-1),le_abs_self (Real.sqrt V-1),
        neg_abs_le (ρ-1),le_abs_self (ρ-1)]
    _ ≤ _ := add_le_add (hsV.trans hV) hρ
  have hx : u*(Real.sqrt V/ρ)-u = u*(Real.sqrt V-ρ)/ρ := by
    field_simp [hρ'.ne'] <;> ring
  rw [hx,abs_div,abs_mul,abs_of_pos hu',abs_of_pos hρ',div_le_iff₀ hρ']
  have hmul := mul_le_mul_of_nonneg_left htri hu'.le
  have huK : u*(2/K) ≤ 1/16 := by
    rw [← mul_div_assoc, div_le_iff₀ hK']
    linarith only [hK]
  have hu75 : u*(1/(75*u)) = 1/75 := by field_simp [hu'.ne']
  rw [mul_add, hu75] at hmul
  linarith only [hmul,huK,hρlo]

end CubeMD
#print axioms CubeMD.singleThreshold_stable
#print axioms CubeMD.scale_displacement_of_ratios
