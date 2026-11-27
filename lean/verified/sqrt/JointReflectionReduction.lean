import ReflectedEndpointReduction
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
namespace CubeBrownian

def JointEndpointReflection {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Z M : Ω → ℝ) (T : ℝ≥0) : Prop :=
  ∀ x ≥ 0, (μ.restrict {w | x < M w}).map Z =
    (gaussianReal 0 (2*T)).restrict (Ioi x) +
      (((gaussianReal 0 (2*T)).restrict (Ioi x)).map (fun z ↦ 2*x-z))

theorem gaussian_terminal_normalizers (T : ℝ≥0) :
    (∫ z, Real.exp (-(z/2)) ∂(gaussianReal 0 (2*T))) = Real.exp ((T:ℝ)/4) ∧
    (∫ z, Real.exp (z/2) ∂(gaussianReal 0 (2*T))) = Real.exp ((T:ℝ)/4) := by
  have calcM (a : ℝ) (ha : a = -1/2 ∨ a = 1/2) :
      mgf (fun y : ℝ ↦ y) (gaussianReal 0 (2*T)) a = Real.exp ((T:ℝ)/4) := by
    rw [mgf_fun_id_gaussianReal]
    push_cast
    congr 1
    rcases ha with rfl | rfl <;> ring
  constructor
  · have hf : (fun z : ℝ ↦ Real.exp (-(z/2))) =
        fun z ↦ Real.exp ((-1/2)*z) := by funext z; congr 1; ring
    rw [hf]
    exact calcM _ (Or.inl rfl)
  · have hf : (fun z : ℝ ↦ Real.exp (z/2)) =
        fun z ↦ Real.exp ((1/2)*z) := by funext z; congr 1; ring
    rw [hf]
    exact calcM _ (Or.inr rfl)

theorem tilted_endpoint_split_of_joint_reflection {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Z M : Ω → ℝ) (T : ℝ≥0)
    (hZ : Measurable Z) (hM : Measurable M)
    (hZlaw : μ.map Z = gaussianReal 0 (2*T))
    (hR : JointEndpointReflection μ Z M T) :
    HasTiltedEndpointSplit (μ.tilted (fun w ↦ -(Z w/2))) M T := by
  let G := gaussianReal 0 (2*T)
  let c := Real.exp ((T:ℝ)/4)
  let fNeg : ℝ → ℝ≥0∞ := fun z ↦ ENNReal.ofReal (Real.exp (-(z/2))/c)
  let fPos : ℝ → ℝ≥0∞ := fun z ↦ ENNReal.ofReal (Real.exp (z/2)/c)
  have hmNeg : Measurable fNeg := by dsimp only [fNeg]; fun_prop
  have hmPos : Measurable fPos := by dsimp only [fPos]; fun_prop
  have hNorm : (∫ w, Real.exp (-(Z w/2)) ∂μ) = c := by
    have hEq : (∫ z, Real.exp (-(z/2)) ∂(μ.map Z)) = ∫ w, Real.exp (-(Z w/2)) ∂μ :=
      integral_map hZ.aemeasurable (by fun_prop)
    rw [hZlaw] at hEq
    exact hEq.symm.trans (gaussian_terminal_normalizers T).1
  intro x hx
  let E := {w | x < M w}
  have hE : MeasurableSet E := measurableSet_lt measurable_const hM
  have hA : (μ.tilted (fun w ↦ -(Z w/2))) E = ∫⁻ z, fNeg z ∂((μ.restrict E).map Z) := by
    rw [tilted_apply' _ _ hE, hNorm, lintegral_map hmNeg hZ]
  have hminus : (G.tilted (fun z ↦ -(z/2))) (Ioi x) =
      ∫⁻ z, fNeg z ∂(G.restrict (Ioi x)) := by
    rw [tilted_apply' _ _ measurableSet_Ioi, gaussian_terminal_normalizers T |>.1]
  have hplus : (G.tilted (fun z ↦ z/2)) (Ioi x) =
      ∫⁻ z, fPos z ∂(G.restrict (Ioi x)) := by
    rw [tilted_apply' _ _ measurableSet_Ioi, gaussian_terminal_normalizers T |>.2]
  change (μ.tilted (fun w ↦ -(Z w/2))) E =
    (G.tilted (fun z ↦ -(z/2))) (Ioi x) + ENNReal.ofReal (Real.exp (-x)) *
      (G.tilted (fun z ↦ z/2)) (Ioi x)
  rw [hA, hR x hx, lintegral_add_measure, hminus, hplus,
    lintegral_map hmNeg (by fun_prop), ← lintegral_const_mul _ hmPos]
  congr 1
  apply lintegral_congr
  intro z
  dsimp only [fNeg,fPos]
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← mul_div_assoc,
    ← Real.exp_add, show -( (2*x-z)/2) = -x+z/2 by ring]

theorem tilted_expectation_of_joint_reflection {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z M : Ω → ℝ)
    (T : ℝ≥0) (hT : 0 < T) (hZ : Measurable Z) (hM : Measurable M)
    (h0 : 0 ≤ᵐ[μ] M) (hLaw : μ.map Z = gaussianReal 0 (2*T))
    (hR : JointEndpointReflection μ Z M T) :
    (∫ w, Real.exp (M w) ∂(μ.tilted (fun w ↦ -(Z w/2)))) =
      maxExpFormula (T:ℝ) := by
  let ν := μ.tilted (fun w ↦ -(Z w/2))
  have hf : Measurable (fun z : ℝ ↦ Real.exp (-(z/2))) := by fun_prop
  have hI : Integrable (fun z : ℝ ↦ Real.exp (-(z/2))) (μ.map Z) := by
    rw [hLaw]
    have he : (fun z : ℝ ↦ Real.exp (-(z/2))) = (fun z ↦ Real.exp ((-1/2:ℝ)*z)) := by
      funext z; congr 1; ring
    rw [he]
    exact integrable_exp_mul_gaussianReal _
  have hInt : Integrable (fun w ↦ Real.exp (-(Z w/2))) μ :=
    (integrable_map_measure hf.aestronglyMeasurable hZ.aemeasurable).mp hI
  haveI : IsProbabilityMeasure ν := isProbabilityMeasure_tilted hInt
  have h0' : 0 ≤ᵐ[ν] M := (tilted_absolutelyContinuous _ _).ae_le h0
  have ht : 0 < (T:ℝ) := by exact_mod_cast hT
  exact integral_exp_of_reflected_tail ν M (T:ℝ) ht hM.aemeasurable h0'
    (reflected_tail_of_endpoint_split ν M T hT
      (tilted_endpoint_split_of_joint_reflection μ Z M T hZ hM hLaw hR))
end CubeBrownian
#print axioms CubeBrownian.tilted_expectation_of_joint_reflection
