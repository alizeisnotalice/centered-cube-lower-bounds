import MeshAsymptotic
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace CubeBrownian

noncomputable def paperMeshGridMax {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (k : ℝ≥0) (n : ℕ) (w : Ω) : ℝ :=
  ⨆ i : Fin (n^3+1), Real.sqrt (2*(k:ℝ)) *
    B (cellLeft (1/((n:ℝ≥0)^2)) i) w - (k:ℝ)*(cellLeft (1/((n:ℝ≥0)^2)) i : ℝ)

theorem paperMesh_uniform_expectation {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B μ)
    {lo hi : ℝ≥0} (hlo : 0 < lo) (hhi : 0 < hi) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ k ∈ Icc lo hi,
      |(∫ w, Real.exp (paperMeshGridMax B k n w) ∂μ)/(n:ℝ) - (k:ℝ)| < ε := by
  obtain ⟨Y,hY,hmY,hE⟩ := brownian_measurable_version μ hB
  have hYint (k : ℝ≥0) (n : ℕ) : (∫ w, Real.exp (paperMeshGridMax B k n w) ∂μ) =
      ∫ w, Real.exp (paperMeshGridMax Y k n w) ∂μ := by
    apply integral_congr_ae
    filter_upwards [hE] with w hw
    simp only [paperMeshGridMax,hw]
  have e : 0 < ε/2 := by positivity
  have loR : 0 < (lo:ℝ) := by exact_mod_cast hlo
  have hiR : 0 < (hi:ℝ) := by exact_mod_cast hhi
  have hM := mesh_error_uniform_bound loR hiR (ε/2) e
  have hF := (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually
    (maxExpFormula_div_uniform loR hiR (ε/2) e)
  filter_upwards [hM,hF] with n hn hnF k hk
  have hkR : (k:ℝ) ∈ Icc (lo:ℝ) (hi:ℝ) := ⟨by exact_mod_cast hk.1,by exact_mod_cast hk.2⟩
  obtain ⟨hnpos,hδ,herr⟩ := hn k hkR
  let A : ℝ≥0 := k/(n:ℝ≥0)^2
  let N : ℕ := n^3
  let δ := (Real.sqrt (n:ℝ))⁻¹
  let b := (hi:ℝ)/(n:ℝ)^2
  have hkpos : 0 < k := hlo.trans_le hk.1
  have hA : 0 < A := by dsimp [A]; positivity
  have hN : 0 < N := by dsimp [N]; positivity
  have hAr : (A:ℝ) ≤ b := by
    dsimp [A,b]
    push_cast
    gcongr
    exact hkR.2
  let C := fun t w ↦ (Real.sqrt ((k⁻¹:ℝ≥0):ℝ))⁻¹ * Y (k⁻¹*t) w
  have hC : IsBrownianReal C μ := hY.smul (c:=k⁻¹) (by positivity)
  have hmC (t : ℝ≥0) : Measurable (C t) := measurable_const.mul (hmY (k⁻¹*t))
  have hTime : (cellLeft A N : ℝ) = (k:ℝ)*(n:ℝ) := by
    have hnz : (n:ℝ) ≠ 0 := by exact_mod_cast hnpos.ne'
    dsimp [cellLeft,A,N]
    push_cast
    field_simp
  have hZero : ∀ᵐ w ∂μ, C 0 w = 0 := hC.toIsPreBrownianReal.eval_zero_ae_eq_zero
  have hgrid : meshGridMax C A N =ᵐ[μ] paperMeshGridMax Y k n := by
    filter_upwards [hZero] with w hw
    change (⨆ i : Fin (n^3+1), driftedCentered C w (cellLeft A i)) =
      ⨆ i : Fin (n^3+1), Real.sqrt (2*(k:ℝ))*Y (cellLeft (1/(n:ℝ≥0)^2) i) w -
        (k:ℝ)*(cellLeft (1/(n:ℝ≥0)^2) i:ℝ)
    congr 1
    funext i
    have hleft : cellLeft A i = k*cellLeft (1/(n:ℝ≥0)^2) i := by
      dsimp [cellLeft,A]
      ring
    have hCoeff : Real.sqrt 2 * (Real.sqrt ((k⁻¹:ℝ≥0):ℝ))⁻¹ = Real.sqrt (2*(k:ℝ)) := by
      push_cast
      rw [Real.sqrt_inv,inv_inv,Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
    rw [driftedCentered,centeredScaled,hw,sub_zero,hleft]
    dsimp only [C]
    rw [← mul_assoc, hCoeff,← mul_assoc,inv_mul_cancel₀ hkpos.ne',one_mul]
    rfl
  have hEq : (∫ w, Real.exp (meshGridMax C A N w) ∂μ) =
      ∫ w, Real.exp (paperMeshGridMax Y k n w) ∂μ :=
    integral_congr_ae (hgrid.mono (fun _ h ↦ congrArg Real.exp h))
  have hAct := actual_weighted_grid_error μ hC hmC A hA N hN b δ hAr hδ
  dsimp only at hAct
  rw [hTime,hEq,← hYint] at hAct
  let H := ∫ w, Real.exp (paperMeshGridMax B k n w) ∂μ
  let F := maxExpFormula ((k:ℝ)*(n:ℝ))
  have hloE : 0 ≤ F-H := hAct.1
  have hhiE : (F-H)/(n:ℝ) < ε/2 := by
    apply lt_of_le_of_lt (div_le_div_of_nonneg_right hAct.2 (Nat.cast_nonneg n))
    change ((1-Real.exp (-δ))*F + 8*(N:ℝ)*((N:ℝ)+1)*Real.exp (δ-δ^2/(8*b)))/(n:ℝ) < _
    dsimp [N,F]
    push_cast
    exact herr
  have hCont : |F/(n:ℝ)-(k:ℝ)| < ε/2 := hnF k hkR
  have h1 : H/(n:ℝ)-(k:ℝ) = (F/(n:ℝ)-(k:ℝ)) - (F-H)/(n:ℝ) := by ring
  rw [h1]
  have hAbs := abs_sub_le (F/(n:ℝ)-(k:ℝ)) 0 ((F-H)/(n:ℝ))
  simp only [sub_zero,zero_sub,abs_neg] at hAbs
  rw [abs_of_nonneg (div_nonneg hloE (Nat.cast_nonneg n))] at hAbs
  linarith only [hAbs,hCont,hhiE]

theorem paperMesh_supremum_tendsto {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B μ)
    {lo hi : ℝ≥0} (hlo : 0 < lo) (hhi : 0 < hi) (hle : lo ≤ hi) :
    Tendsto (fun n : ℕ ↦ ⨆ k : Icc lo hi,
      |(∫ w, Real.exp (paperMeshGridMax B k.1 n w) ∂μ)/(n:ℝ)-(k.1:ℝ)|) atTop (𝓝 0) := by
  let _ : Nonempty (Icc lo hi) := ⟨⟨lo,le_rfl,hle⟩⟩
  apply Metric.tendsto_nhds.2
  intro ε hε
  filter_upwards [paperMesh_uniform_expectation μ hB hlo hhi (ε/2) (by positivity)] with n hn
  let f (k : Icc lo hi) := |(∫ w, Real.exp (paperMeshGridMax B k.1 n w) ∂μ)/(n:ℝ)-(k.1:ℝ)|
  have h (k : Icc lo hi) : f k ≤ ε/2 := (hn k.1 k.2).le
  have hb : BddAbove (range f) := by
    refine ⟨ε/2,?_⟩
    rintro x ⟨k,rfl⟩
    exact h k
  have hl : 0 ≤ ⨆ k, f k := (abs_nonneg _).trans (le_ciSup hb (⟨lo,le_rfl,hle⟩ : Icc lo hi))
  change dist (⨆ k, f k) 0 < ε
  rw [Real.dist_eq,sub_zero,abs_of_nonneg hl]
  exact (ciSup_le h).trans_lt (by linarith only [hε])

theorem paperMesh_exact_interval {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B μ) :
    Tendsto (fun n : ℕ ↦ ⨆ k : Icc (261/121:ℝ≥0) (261/100:ℝ≥0),
      |(∫ w, Real.exp (paperMeshGridMax B k.1 n w) ∂μ)/(n:ℝ)-(k.1:ℝ)|) atTop (𝓝 0) := by
  apply paperMesh_supremum_tendsto μ hB
  · norm_num
  · norm_num
  · have hh : ((261/121:ℝ≥0):ℝ) ≤ ((261/100:ℝ≥0):ℝ) := by
      push_cast
      norm_num
    exact_mod_cast hh
end CubeBrownian
#print axioms CubeBrownian.paperMesh_exact_interval
