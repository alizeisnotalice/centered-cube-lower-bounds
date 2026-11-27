import ActualMeshGeometry
import AnchorCellBound
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace CubeBrownian

theorem driftedCentered_exp_normalized {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) (t : ℝ≥0) :
    (∫ w, Real.exp (driftedCentered B w t) ∂μ) = 1 := by
  let Z := fun w ↦ centeredScaled B w t
  have hZ := centeredScaled_law hB t
  have h : (∫ x, Real.exp x ∂(μ.map Z)) = ∫ w, Real.exp (Z w) ∂μ :=
    integral_map hZ.aemeasurable Real.measurable_exp.aestronglyMeasurable
  rw [hZ.map_eq] at h
  have hg : (∫ w, Real.exp (Z w) ∂μ) = Real.exp (t:ℝ) := by
    change (∫ w, Real.exp (Z w) ∂μ) = _
    calc
      _ = mgf (fun x : ℝ ↦ x) (gaussianReal 0 (2*t)) 1 := by simpa [mgf, Z] using h.symm
      _ = _ := by rw [mgf_fun_id_gaussianReal]; push_cast; congr 1; ring
  change (∫ w, Real.exp (Z w-(t:ℝ)) ∂μ) = _
  simp_rw [sub_eq_add_neg,Real.exp_add,mul_comm _ (Real.exp (-(t:ℝ)))]
  rw [integral_const_mul,hg,← Real.exp_add,neg_add_cancel,Real.exp_zero]

theorem meshModulus_anchor_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B μ)
    (hmB : ∀ t, Measurable (B t)) (A : ℝ≥0) (hA : 0 < A) (N : ℕ) (hN : 0 < N)
    (j : Fin (N+1)) (b x : ℝ) (hb : (A:ℝ) ≤ b) (hx : b < x) :
    (μ.tilted (fun w ↦ driftedCentered B w (cellLeft A j)))
      {w | x < meshModulus B A N w} ≤
      (4*(N:ℝ≥0∞))*ENNReal.ofReal (Real.exp (-((x-b)^2)/(4*b))) := by
  let Tj := cellLeft A (j:ℕ)
  let L := fun w ↦ driftedCentered B w Tj
  let Q := μ.tilted L
  let E (i : Fin N) := {w | x < meshCellModulus B (cellLeft A i) A w}
  let K := ENNReal.ofReal (Real.exp (-((x-b)^2)/(4*b)))
  have hQ : Q = anchorTiltedMeasure μ B (Real.sqrt 2) 1 Tj := by
    dsimp only [Q,L,driftedCentered,anchorTiltedMeasure,centeredScaled]
    rw [tilt_sub_const]
    simp
  let _ : Nonempty (Fin N) := ⟨⟨0,hN⟩⟩
  have hPath : ∀ᵐ w ∂Q, Continuous (B · w) := (tilted_absolutelyContinuous μ L).ae_le hB.cont
  have hEq : {w | x < meshModulus B A N w} = ⋃ i, E i := by
    ext w
    simp only [meshModulus,E,mem_ofPred_eq, mem_iUnion]
    exact lt_ciSup_iff (finite_range _).bddAbove
  have hBnd (i : Fin N) : Q (E i) ≤ 4*K := by
    have hi : Tj ≤ cellLeft A i ∨ cellLeft A i+A ≤ Tj := by
      by_cases hj : (j:ℕ) ≤ (i:ℕ)
      · exact Or.inl (by unfold Tj cellLeft; gcongr)
      · rw [← cellLeft_succ]
        exact Or.inr (by unfold Tj cellLeft; gcongr; omega)
    have he : E i =ᵐ[Q]
        {w | ∃ s ≤ A, x < |driftedCentered B w (cellLeft A i+s)-driftedCentered B w (cellLeft A i)|} := by
      filter_upwards [hPath] with w hw
      exact meshCellModulus_spec B w hw _ A hA x
    rw [measure_congr he,hQ]
    exact anchorCell_drifted_bound μ hB hmB Tj (cellLeft A i) A hA hi b x hb hx
  change Q {w | x < meshModulus B A N w} ≤ _
  rw [hEq]
  calc
    Q (⋃ i, E i) ≤ ∑ i, Q (E i) := measure_iUnion_fintype_le Q E
    _ ≤ ∑ _ : Fin N, 4*K := Finset.sum_le_sum (fun i _ ↦ hBnd i)
    _ = _ := by simp [K,mul_assoc, mul_left_comm]
end CubeBrownian
#print axioms CubeBrownian.meshModulus_anchor_tail
