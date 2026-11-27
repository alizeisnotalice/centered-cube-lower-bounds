/-
The `n`-fold tensor of the Rudin–Shapiro density, and its mass.

The manuscript uses the tensor test function `f_n(x) = ∏_{i<n} ρ_K(x_i)` and
computes `‖f_n‖₁ = (2n²)ⁿ` on the box `[-n², n²]ⁿ`.  This file proves:

- `integral_prod_rho_box`: `∫_{[-R,R]ⁿ} ∏_i ρ_K(x_i) dx = (2R)ⁿ`, by Fubini for
  product measures (`integral_fintype_prod_eq_prod`) together with the
  one-dimensional computation `∫_{-R}^{R} ρ_K = 2R` of `Periodic.lean`;
- `absMass_indicator_tensorRho`: the same as an `absMass`, i.e. the literal
  `HaloData.mass` shape `‖1_{[-R,R]ⁿ} f_n‖₁ = (2R)ⁿ`.

This is the mass half of `lem:transfer`; the superlevel-set measure half (the
periodic lift) is still open.
-/
import Mathlib.MeasureTheory.Integral.Pi
import Cubes
import Periodic

open MeasureTheory

namespace CenteredCube

/-- The box `[-R,R]ⁿ` is the product of the intervals `[-R,R]`. -/
theorem box_eq_pi (n : ℕ) (R : ℝ) :
    box n R = Set.univ.pi (fun _ : Fin n => Set.Icc (-R) R) := by
  ext x
  simp only [box, Set.mem_Icc, Set.mem_pi, Set.mem_univ, forall_true_left]
  constructor
  · intro h i
    exact ⟨h.1 i, h.2 i⟩
  · intro h
    exact ⟨fun i => (h i).1, fun i => (h i).2⟩

/-- The box `[-R,R]ⁿ` is closed, hence measurable. -/
theorem measurableSet_box (n : ℕ) (R : ℝ) : MeasurableSet (box n R) :=
  isClosed_Icc.measurableSet

namespace RudinDensity

/-- The `n`-fold tensor of `ρ_K`: the manuscript's periodic test density. -/
noncomputable def tensorRho (K n : ℕ) (x : Space n) : ℝ := ∏ i, rho K (x i)

/-- The tensor density is positive: every factor is at least `1/2`. -/
theorem tensorRho_pos {K : ℕ} (hK : 1 ≤ K) (n : ℕ) (x : Space n) :
    0 < tensorRho K n x := by
  refine Finset.prod_pos (fun i _ => ?_)
  have := (rho_bounds hK (x i)).1
  linarith

/-- The tensor density is continuous. -/
theorem continuous_tensorRho {K : ℕ} (hK : 1 ≤ K) (n : ℕ) :
    Continuous (tensorRho K n) := by
  unfold tensorRho
  simpa using continuous_finsetProd (Finset.univ : Finset (Fin n))
    (fun i _ => (continuous_rho hK).comp (continuous_apply i))

/-- **The mass of the tensor density on the box.**  Fubini plus the
one-dimensional computation `∫_{-R}^{R} ρ_K = 2R`:

`∫_{[-R,R]ⁿ} ∏_{i<n} ρ_K(x_i) dx = (2R)ⁿ`. -/
theorem integral_prod_rho_box {K n : ℕ} (hK : 1 ≤ K) (R : ℕ) :
    ∫ x in box n (R : ℝ), ∏ i : Fin n, rho K (x i) = (2 * (R : ℝ)) ^ n := by
  have hR : (0 : ℝ) ≤ (R : ℝ) := Nat.cast_nonneg R
  rw [box_eq_pi n (R : ℝ)]
  rw [show (volume : Measure (Space n)) = Measure.pi (fun _ : Fin n => volume) from volume_pi]
  rw [MeasureTheory.Measure.restrict_pi_pi]
  rw [integral_fintype_prod_eq_prod]
  have h1 : ∀ _i : Fin n, (∫ x : ℝ, rho K x ∂(volume.restrict (Set.Icc (-(R:ℝ)) (R:ℝ))))
      = 2 * (R : ℝ) := by
    intro _
    rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith : -(R:ℝ) ≤ (R:ℝ))]
    exact integral_rho_box hK R
  rw [Finset.prod_congr rfl (fun i _ => h1 i), Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

/-- **`‖1_{[-R,R]ⁿ} f_n‖₁ = (2R)ⁿ`** — the mass field of `HaloData`, in the
`absMass` (lower-integral) form used by the maximal operator. -/
theorem absMass_indicator_tensorRho {K n : ℕ} (hK : 1 ≤ K) (R : ℕ) :
    absMass ((box n (R : ℝ)).indicator (tensorRho K n))
      = ENNReal.ofReal ((2 * (R : ℝ)) ^ n) := by
  have hcont : Continuous (tensorRho K n) := continuous_tensorRho hK n
  have hIntOn : IntegrableOn (tensorRho K n) (box n (R : ℝ)) volume :=
    hcont.integrableOn_Icc
  have hnonneg : 0 ≤ᵐ[volume.restrict (box n (R : ℝ))] tensorRho K n :=
    Filter.Eventually.of_forall (fun x => (tensorRho_pos hK n x).le)
  unfold absMass
  have hpt : ∀ y : Space n,
      ENNReal.ofReal |(box n (R : ℝ)).indicator (tensorRho K n) y|
        = (box n (R : ℝ)).indicator (fun y => ENNReal.ofReal (tensorRho K n y)) y := by
    intro y
    by_cases hy : y ∈ box n (R : ℝ)
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy,
        abs_of_pos (tensorRho_pos hK n y)]
    · simp [Set.indicator, hy]
  simp only [hpt]
  have hbox : box n (R : ℝ) = Set.Icc (fun _ : Fin n => -(R:ℝ)) (fun _ => (R:ℝ)) := rfl
  rw [hbox] at hIntOn hnonneg ⊢
  rw [lintegral_indicator measurableSet_Icc,
    ← ofReal_integral_eq_lintegral_ofReal hIntOn hnonneg]
  congr 1
  exact integral_prod_rho_box hK R

end RudinDensity
end CenteredCube

#print axioms CenteredCube.box_eq_pi
#print axioms CenteredCube.RudinDensity.tensorRho_pos
#print axioms CenteredCube.RudinDensity.continuous_tensorRho
#print axioms CenteredCube.RudinDensity.integral_prod_rho_box
#print axioms CenteredCube.RudinDensity.absMass_indicator_tensorRho
