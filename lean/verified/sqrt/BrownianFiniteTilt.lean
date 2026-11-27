import GaussianTilt
import ProductTilt
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
namespace CubeBrownian

theorem finite_partition_terminal_tilt {ι : Type*} [Fintype ι]
    (duration : ι → ℝ≥0) (hd : ∀ i, 0 < duration i) :
    (Measure.pi (fun i ↦ gaussianReal 0 (2*duration i))).tilted
      (fun x : ι → ℝ ↦ (-1/2)*(∑ i, x i)) =
      Measure.pi (fun i ↦ gaussianReal (-(duration i : ℝ)) (2*duration i)) := by
  have hInt (i : ι) : Integrable (fun x ↦ Real.exp ((-1/2:ℝ)*x)) (gaussianReal 0 (2*duration i)) :=
    integrable_exp_mul_gaussianReal _
  have hh := CubeMD.tilted_pi_eq_pi_tilted (fun i ↦ gaussianReal 0 (2*duration i))
      (fun _ ↦ id) (-1/2) hInt
  simp only [id_eq] at hh
  rw [hh]
  congr 1
  funext i
  have hEq : (fun x : ℝ ↦ (-1/2)*x) = fun x ↦ -(x/2) := by
    funext x
    ring
  rw [hEq, endpoint_brownian_tilt (duration i) (hd i)]
end CubeBrownian
#print axioms CubeBrownian.finite_partition_terminal_tilt
