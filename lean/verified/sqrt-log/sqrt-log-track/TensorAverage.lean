import Product
import HitProduct

open MeasureTheory Set
open scoped ENNReal
namespace CenteredCube.RudinDensity

theorem rho_add_int (K : ℕ) (x : ℝ) (m : ℤ) : rho K (x + m) = rho K x := by
  cases m with
  | ofNat k => exact periodic_add_nat (rho_add_one K) k x
  | negSucc k =>
    simpa only [Int.cast_negSucc, sub_eq_add_neg, Nat.cast_succ] using
      periodic_sub_nat (rho_add_one K) (k+1) x

theorem tensorRho_add_int (K n : ℕ) (x : Space n) (z : Fin n → ℤ) :
    tensorRho K n (fun i ↦ x i + (z i : ℝ)) = tensorRho K n x := by
  unfold tensorRho
  exact Finset.prod_congr rfl (fun i _ ↦ rho_add_int K (x i) (z i))

theorem cube_eq_pi_closed {n : ℕ} (x : Space n) (r : ℝ) :
    cube x r = Set.univ.pi (fun i ↦ Icc (x i-r/2) (x i+r/2)) := by
  ext y
  simp only [cube, Set.mem_Icc, Set.mem_pi, Set.mem_univ, forall_true_left]
  exact ⟨fun ⟨hl,hu⟩ i ↦ ⟨hl i,hu i⟩, fun h ↦ ⟨fun i ↦ (h i).1, fun i ↦ (h i).2⟩⟩

theorem integral_tensorRho_cube {K n : ℕ} (hK : 1 ≤ K) (x : Space n)
    (r : ℝ) (hr : 0 ≤ r) :
    ∫ y in cube x r, tensorRho K n y =
      ∏ i, (∫ y in (x i-r/2)..(x i+r/2), rho K y) := by
  rw [cube_eq_pi_closed]
  unfold tensorRho
  rw [show (volume : Measure (Space n)) = Measure.pi (fun _ : Fin n ↦ volume) from volume_pi,
    Measure.restrict_pi_pi, integral_fintype_prod_eq_prod]
  apply Finset.prod_congr rfl
  intro i _
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith : x i-r/2 ≤ x i+r/2)]

theorem cubeAverage_tensor_factor {K n : ℕ} (hK : 1 ≤ K) (x : Space n)
    (r : ℝ) (hr : 0 < r) :
    cubeAverage (tensorRho K n) x r =
      ENNReal.ofReal (∏ i, (1/r)*(∫ y in (x i-r/2)..(x i+r/2), rho K y)) := by
  have hInt : IntegrableOn (tensorRho K n) (cube x r) volume :=
    (continuous_tensorRho hK n).integrableOn_Icc
  have hNN : 0 ≤ᵐ[volume.restrict (cube x r)] tensorRho K n :=
    Filter.Eventually.of_forall (fun y ↦ (tensorRho_pos hK n y).le)
  unfold cubeAverage
  simp_rw [abs_of_pos (tensorRho_pos hK n _)]
  rw [← ofReal_integral_eq_lintegral_ofReal hInt hNN,
    ← ENNReal.ofReal_pow hr.le, ← ENNReal.ofReal_div_of_pos (pow_pos hr _),
    integral_tensorRho_cube hK x r hr.le]
  congr 1
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, one_div,
    inv_pow, div_eq_mul_inv, mul_comm]

theorem unit_cell_mass_tensorRho {K n : ℕ} (hK : 1 ≤ K) :
    ∫⁻ x in Set.univ.pi (fun _ : Fin n ↦ Ioc (0:ℝ) 1),
      ENNReal.ofReal |tensorRho K n x| ∂volume = 1 := by
  let U := Set.univ.pi (fun _ : Fin n ↦ Ioc (0:ℝ) 1)
  have hsub : U ⊆ Set.Icc (fun _ : Fin n ↦ (0:ℝ)) (fun _ : Fin n ↦ 1) := by
    intro x hx
    exact ⟨fun i ↦ ((Set.mem_pi.mp hx) i trivial).1.le, fun i ↦ ((Set.mem_pi.mp hx) i trivial).2⟩
  have hInt : IntegrableOn (tensorRho K n) U volume :=
    (continuous_tensorRho hK n).integrableOn_Icc.mono_set hsub
  have hNN : 0 ≤ᵐ[volume.restrict U] tensorRho K n :=
    Filter.Eventually.of_forall (fun y ↦ (tensorRho_pos hK n y).le)
  change (∫⁻ x in U, ENNReal.ofReal |tensorRho K n x| ∂volume) = 1
  simp_rw [abs_of_pos (tensorRho_pos hK n _)]
  rw [← ofReal_integral_eq_lintegral_ofReal hInt hNN]
  have hM : ∫ x in U, tensorRho K n x ∂volume = 1 := by
    dsimp only [U, tensorRho]
    rw [show (volume : Measure (Space n)) = Measure.pi (fun _ : Fin n ↦ volume) from volume_pi,
      Measure.restrict_pi_pi, integral_fintype_prod_eq_prod]
    have he : (∫ y in Ioc (0:ℝ) 1, rho K y ∂volume) = 1 := by
      rw [← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
      exact integral_rho K hK
    simp only [he, Finset.prod_const_one]
  rw [hM, ENNReal.ofReal_one]

theorem hitPoint_cubeAverage_witness {n K : ℕ} (hK : 4 ≤ K) (hn : 0 < n) {t : ℝ}
    (hu : 1 ≤ centerScale n K) (hKu : 32*centerScale n K ≤ (K:ℝ))
    (ht : |t-(K:ℝ)/4| ≤ (K:ℝ)/(100*centerScale n K))
    (hErr : 72*scoreB^3*(2*centerScale n K)^3/Real.sqrt (n:ℝ) ≤ 1)
    {x : Space n} (hx : x ∈ hitPoint n K t) :
    0 < rfun K t ∧ rfun K t ≤ 2 ∧
    ENNReal.ofReal (Real.exp (centerScale n K^2/2-2)) <
      cubeAverage (tensorRho K n) x (rfun K t) := by
  obtain ⟨hr,hrU,hP⟩ := hitPoint_intervalAverage_witness hK hn hu hKu ht hErr hx
  refine ⟨hr,hrU,?_⟩
  rw [cubeAverage_tensor_factor (by omega : 1 ≤ K) x _ hr]
  exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (Real.exp_pos _).le).2 hP

theorem interval_rho_add_int (K : ℕ) (a b : ℝ) (m : ℤ) :
    (∫ y in (a+(m:ℝ))..(b+(m:ℝ)), rho K y) = ∫ y in a..b, rho K y := by
  rw [← intervalIntegral.integral_comp_add_right (rho K)]
  simp_rw [rho_add_int]

theorem cubeAverage_tensor_add_int {K n : ℕ} (hK : 1 ≤ K) (x : Space n)
    (z : Fin n → ℤ) (r : ℝ) (hr : 0 < r) :
    cubeAverage (tensorRho K n) (fun i ↦ x i + (z i:ℝ)) r =
      cubeAverage (tensorRho K n) x r := by
  rw [cubeAverage_tensor_factor hK _ _ hr, cubeAverage_tensor_factor hK _ _ hr]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  change (1/r)*(∫ y in (x i+(z i:ℝ)-r/2)..(x i+(z i:ℝ)+r/2), rho K y) =
    (1/r)*(∫ y in (x i-r/2)..(x i+r/2), rho K y)
  rw [show x i+(z i:ℝ)-r/2 = (x i-r/2)+(z i:ℝ) by ring,
      show x i+(z i:ℝ)+r/2 = (x i+r/2)+(z i:ℝ) by ring,
      interval_rho_add_int]

theorem hitUnion_cubeAverage_witness {n K : ℕ} (hK : 4 ≤ K) (hn : 0 < n)
    {ι : Type*} (t : ι → ℝ)
    (hu : 1 ≤ centerScale n K) (hKu : 32*centerScale n K ≤ (K:ℝ))
    (ht : ∀ j, |t j-(K:ℝ)/4| ≤ (K:ℝ)/(100*centerScale n K))
    (hErr : 72*scoreB^3*(2*centerScale n K)^3/Real.sqrt (n:ℝ) ≤ 1)
    {x : Space n} (hx : x ∈ ⋃ j, hitPoint n K (t j)) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 2 ∧
      ENNReal.ofReal (Real.exp (centerScale n K^2/2-2)) <
        cubeAverage (tensorRho K n) x r := by
  obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hx
  exact ⟨rfun K (t j), hitPoint_cubeAverage_witness hK hn hu hKu (ht j) hErr hj⟩

theorem hitUnion_cubeAverage_witness_translate {n K : ℕ} (hK : 4 ≤ K) (hn : 0 < n)
    {ι : Type*} (t : ι → ℝ)
    (hu : 1 ≤ centerScale n K) (hKu : 32*centerScale n K ≤ (K:ℝ))
    (ht : ∀ j, |t j-(K:ℝ)/4| ≤ (K:ℝ)/(100*centerScale n K))
    (hErr : 72*scoreB^3*(2*centerScale n K)^3/Real.sqrt (n:ℝ) ≤ 1)
    {x : Space n} (hx : x ∈ ⋃ j, hitPoint n K (t j)) (m : Fin n → ℤ) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 2 ∧
      ENNReal.ofReal (Real.exp (centerScale n K^2/2-2)) <
        cubeAverage (tensorRho K n) (fun i ↦ x i + (m i:ℝ)) r := by
  obtain ⟨r,hr,hrU,ha⟩ := hitUnion_cubeAverage_witness hK hn t hu hKu ht hErr hx
  refine ⟨r,hr,hrU,?_⟩
  rw [cubeAverage_tensor_add_int (by omega : 1 ≤ K) x m r hr]
  exact ha

end CenteredCube.RudinDensity
#print axioms CenteredCube.RudinDensity.tensorRho_add_int
#print axioms CenteredCube.RudinDensity.integral_tensorRho_cube
#print axioms CenteredCube.RudinDensity.cubeAverage_tensor_factor
#print axioms CenteredCube.RudinDensity.unit_cell_mass_tensorRho
#print axioms CenteredCube.RudinDensity.hitPoint_cubeAverage_witness
#print axioms CenteredCube.RudinDensity.cubeAverage_tensor_add_int
#print axioms CenteredCube.RudinDensity.hitUnion_cubeAverage_witness_translate
