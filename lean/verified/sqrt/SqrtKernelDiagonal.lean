import SqrtPlateauPolynomial

namespace CenteredCubeSqrt

/-- Deterministic diagonal assembly in paperkernel, preserving the original
(V_{min}) and (r_*). The bounds on the raw atomic and mixed integrals
are separate inputs, not consequences of the algebra here. -/
theorem paper_kernel_diagonal_assembly {L F T G A : ℝ}
    (hl : L ∈ Set.Icc (10/9 : ℝ) (11/9))
    (hTF : 0 ≤ (27/29)*L^2-F ∧ (27/29)*L^2-F ≤ T)
    (hG : |G-F/3| ≤ A) :
    100/261-T/3-A ≤ G ∧
      |G/((27/29)*L^2/3)-1| ≤ (T+3*A)/(100/87) := by
  have floor := (plateau_normalized_bounds hl).1
  have hden : 0 < (27/29)*L^2/3 := by linarith
  have hA : 0 ≤ A := (abs_nonneg _).trans hG
  rcases abs_le.mp hG with ⟨hglo,hghi⟩
  have habs : |G-(27/29)*L^2/3| ≤ T/3+A := by
    apply abs_le.mpr
    constructor <;> linarith [hTF.1,hTF.2]
  constructor
  · linarith [hTF.2]
  · have e : G/((27/29)*L^2/3)-1 = (G-(27/29)*L^2/3)/((27/29)*L^2/3) := by
      rw [sub_div, div_self (ne_of_gt hden)]
    rw [e, abs_div, abs_of_pos hden]
    calc
      _ ≤ (T/3+A)/((27/29)*L^2/3) := div_le_div_of_nonneg_right habs hden.le
      _ ≤ (T/3+A)/(100/261) := by
        apply div_le_div_of_nonneg_left
        · linarith [hTF.1,hTF.2]
        · norm_num
        · linarith
      _ = (T+3*A)/(100/87) := by ring

#print axioms paper_kernel_diagonal_assembly

end CenteredCubeSqrt
