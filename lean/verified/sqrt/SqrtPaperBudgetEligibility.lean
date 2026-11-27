import SqrtPaperParameterRates
import SqrtActualKernelBundle

namespace CenteredCubeSqrt
open Filter Set MvPolynomial
open scoped Topology BigOperators
set_option maxHeartbeats 2000000
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

noncomputable def paperNearBudget (B K E : ℝ) : ℝ := 2/(3*B^2)+2/K+E
noncomputable def paperDiagonalBudget (B K E : ℝ) : ℝ := 1/(3*B^2)+2/K+E
noncomputable def paperPlateauTail (M : ℕ) : ℝ := 48/(29*(M:ℝ)^3)
noncomputable def paperKernelFloor (B K E : ℝ) (M : ℕ) : ℝ :=
  100/261-paperPlateauTail M/3-paperDiagonalBudget B K E
noncomputable def paperKernelRelError (B K E : ℝ) (M : ℕ) : ℝ :=
  (paperPlateauTail M+3*paperDiagonalBudget B K E)/(100/87)

theorem paper_actual_kernel_finite_budgets {w : ℝ} (hw : 4≤w) {v : ℕ→ℝ} {b d : ℕ→ℕ}
    (h : ∀ᶠ n in atTop, PaperMeshParameters w (v n) (b n) (d n))
    (hv : Tendsto v atTop atTop)
    (hK : Tendsto (fun n => (paperPeriod (d n):ℝ)/(v n)^4) atTop atTop)
    (hK0 : Tendsto (fun n => (paperPeriod (d n):ℝ)) atTop atTop) :
    ∀ᶠ n in atTop,
      let B := ((2:ℝ)^(b n))
      let K := (paperPeriod (d n):ℝ)
      let M := paperMeshM (v n)
      let E := paperAtomicCrossSmoothing w K B (v n) M
      paperFarRawBudget B K≤21/500 ∧ E≤1/1000 ∧ paperNearBudget B K E≤1/1000 ∧
        19/50≤paperKernelFloor B K E M := by
  let B (n : ℕ) := (2:ℝ)^(b n)
  let K (n : ℕ) := (paperPeriod (d n):ℝ)
  let M (n : ℕ) := paperMeshM (v n)
  let E (n : ℕ) := paperAtomicCrossSmoothing w (K n) (B n) (v n) (M n)
  have htB : Tendsto B atTop atTop := tendsto_atTop_mono' atTop (h.mono fun _ H => H.label_lower) hv
  have htM : Tendsto (fun n => (M n:ℝ)) atTop atTop :=
    tendsto_atTop_mono' atTop (h.mono fun _ H => H.mesh_sqrt_lower) (Real.tendsto_sqrt_atTop.comp hv)
  have hE0 : Tendsto E atTop (𝓝 0) := by
    have H := (actual_cross_smoothing_rate hw h hK).mul (tendsto_inv_atTop_zero.comp hv)
    rw [mul_zero] at H
    apply H.congr'
    filter_upwards [h] with n hn
    have hv' : v n≠0 := by linarith [hn.v_ge_four]
    change v n*E n*(v n)⁻¹=E n
    field_simp
  have X := paper_kernel_budgets_tendsto B K (fun n => (M n:ℝ)) E
    (tendsto_inv_atTop_zero.comp htB) (tendsto_inv_atTop_zero.comp hK0)
    (tendsto_inv_atTop_zero.comp htM) hE0
  exact normalized_kernel_eventually_finite_budgets X.1 hE0 X.2.1 X.2.2

theorem paper_actual_relative_error_scaled {w : ℝ} (hw : 4≤w) {v : ℕ→ℝ} {b d : ℕ→ℕ}
    (h : ∀ᶠ n in atTop, PaperMeshParameters w (v n) (b n) (d n))
    (hv : Tendsto v atTop atTop)
    (hK : Tendsto (fun n => (paperPeriod (d n):ℝ)/(v n)^4) atTop atTop)
    (hK1 : Tendsto (fun n => (paperPeriod (d n):ℝ)/v n) atTop atTop) :
    Tendsto (fun n =>
      let B := ((2:ℝ)^(b n))
      let K := (paperPeriod (d n):ℝ)
      let M := paperMeshM (v n)
      let E := paperAtomicCrossSmoothing w K B (v n) M
      v n*paperKernelRelError B K E M) atTop (𝓝 (87/(50*w))) := by
  let B (n : ℕ) := (2:ℝ)^(b n)
  let K (n : ℕ) := (paperPeriod (d n):ℝ)
  let M (n : ℕ) := paperMeshM (v n)
  let E (n : ℕ) := paperAtomicCrossSmoothing w (K n) (B n) (v n) (M n)
  have X := paper_mesh_scaled_vanishing h hv hK1
  have Y := actual_cross_smoothing_rate hw h hK
  have Z := (((X.2.2.const_mul (48/29:ℝ))).add
    ((((X.1.const_mul (1/3:ℝ)).add (X.2.1.const_mul 2)).add Y).const_mul 3)).div_const (100/87)
  have hw0 : w≠0 := by linarith
  have W : ((48/29:ℝ)*0+3*((1/3:ℝ)*0+2*0+2/(3*w)))/(100/87)=87/(50*w) := by
    field_simp
    ring
  rw [W] at Z
  apply Z.congr
  intro n
  dsimp only
  change ((48/29)*(v n/(M n:ℝ)^3)+3*((1/3)*(v n/(B n)^2)+2*(v n/K n)+v n*E n))/(100/87) =
    v n*paperKernelRelError (B n) (K n) (E n) (M n)
  unfold paperKernelRelError paperPlateauTail paperDiagonalBudget
  simp only [div_eq_mul_inv,mul_inv]
  ring

#print axioms paper_actual_kernel_finite_budgets
#print axioms paper_actual_relative_error_scaled
end CenteredCubeSqrt
