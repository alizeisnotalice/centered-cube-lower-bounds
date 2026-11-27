import SqrtUnitPhaseTaylor
import Mathlib.Analysis.Normed.Group.Basic

namespace CenteredCubeSqrt
open scoped BigOperators
open Complex

/-- The phase remainder keeps real intrabin offsets instead of replacing the
atom positions by the coarse grid. -/
theorem atom_phase_sum_bound {ι : Type*} (s : Finset ι)
    (z : ι → ℂ) (V : ι → ℝ) {t A W : ℝ}
    (hta : 0≤t) (hz : ∀ j∈s, ‖z j‖=1)
    (hV : ∀ j∈s, |V j|≤A/2) (hcancel : ∑ j ∈ s,z j=0)
    (hW : ‖∑ j ∈ s, z j*(V j:ℂ)‖≤W) :
    ‖∑ j ∈ s, z j*Complex.exp (I*((t*V j:ℝ):ℂ))‖ ≤
      t*W+(s.card:ℝ)*t^2*A^2/8 := by
  let R (j : ι) := Complex.exp (I*((t*V j:ℝ):ℂ))-1-I*((t*V j:ℝ):ℂ)
  have he (j : ι) : z j*Complex.exp (I*((t*V j:ℝ):ℂ)) =
      z j+(I*(t:ℂ))*(z j*(V j:ℂ))+z j*R j := by
    unfold R
    push_cast
    ring
  simp_rw [he,Finset.sum_add_distrib,←Finset.mul_sum,hcancel,zero_add]
  refine (norm_add_le _ _).trans ?_
  have e1 : ‖(I*(t:ℂ))*(∑ j ∈ s, z j*(V j:ℂ))‖≤t*W := by
    simp only [norm_mul,Complex.norm_I,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hta,one_mul]
    exact mul_le_mul_of_nonneg_left hW hta
  have e2 : ‖∑ j ∈ s,z j*R j‖ ≤ (s.card:ℝ)*t^2*A^2/8 := by
    refine (norm_sum_le _ _).trans ?_
    calc
      _ ≤ ∑ j ∈ s,t^2*A^2/8 := by
        refine Finset.sum_le_sum (fun j hj => ?_)
        rw [norm_mul,hz j hj,one_mul]
        refine (unit_phase_Taylor_remainder (t*V j)).trans ?_
        have E := pow_le_pow_left₀ (abs_nonneg (V j)) (hV j hj) 2
        rw [sq_abs] at E
        have H := mul_le_mul_of_nonneg_left E (sq_nonneg t)
        nlinarith
      _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]; ring
  exact add_le_add e1 e2

#print axioms atom_phase_sum_bound

end CenteredCubeSqrt
