import GaussianCalculus
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace CubeBrownian

theorem φ_exp (x : ℝ) : φ x = (Real.sqrt (2*Real.pi))⁻¹ * Real.exp (-(x^2)/2) := by
  simp [φ,gaussianPDFReal_def]

lemma affine_div_atTop (T s : ℝ) (hs : 0 < s) :
    Tendsto (fun t : ℝ ↦ (t-T)/s) atTop atTop := by
  apply tendsto_atTop.mpr
  intro r
  filter_upwards [eventually_ge_atTop (r*s+T)] with t ht
  exact (le_div_iff₀ hs).2 (by linarith only [ht])

theorem gaussian_I1_integrable_and_integral (T s : ℝ) (hs : 0 < s) (hs2 : s^2 = 2*T) :
    IntegrableOn (fun t ↦ Real.exp t*Φ (-(t+T)/s)) (Ioi (0:ℝ)) ∧
      (∫ t in Ioi (0:ℝ), Real.exp t*Φ (-(t+T)/s)) = Φ (T/s)-Φ (-T/s) := by
  let q₁ := fun t : ℝ ↦ -(t+T)/s
  let q₂ := fun t : ℝ ↦ (T-t)/s
  let F := fun t : ℝ ↦ Real.exp t*Φ (q₁ t)-Φ (q₂ t)
  have hComp (t : ℝ) : Real.exp t*φ (q₁ t) = φ (q₂ t) := by
    rw [φ_exp,φ_exp]
    rw [← mul_assoc,mul_comm (Real.exp t),mul_assoc,← Real.exp_add]
    congr 2
    dsimp [q₁,q₂]
    field_simp [hs.ne']
    nlinarith only [congrArg (t * ·) hs2]
  have hf (t : ℝ) (_ : t ∈ Ici (0:ℝ)) :
      HasDerivAt F (Real.exp t*Φ (q₁ t)) t := by
    have h1 : HasDerivAt q₁ (-1/s) t := (((hasDerivAt_id t).add_const T).neg).div_const s
    have h2 : HasDerivAt q₂ (-1/s) t := ((hasDerivAt_id t).const_sub T).div_const s
    have hd := ((Real.hasDerivAt_exp t).mul ((hasDerivAt_Φ (q₁ t)).comp t h1)).sub
      ((hasDerivAt_Φ (q₂ t)).comp t h2)
    convert hd using 1
    all_goals (try rfl)
    change Real.exp t*Φ (q₁ t) = Real.exp t*Φ (q₁ t)+ Real.exp t*(φ (q₁ t)*(-1/s)) - φ (q₂ t)*(-1/s)
    rw [← hComp t]
    ring
  have hTail : Tendsto (fun t ↦ Real.exp t*Φ (q₁ t)) atTop (𝓝 0) := by
    let C := -2*T+2*s^2
    have hlim : Tendsto (fun t : ℝ ↦ Real.exp C*Real.exp (-t)) atTop (𝓝 0) := by
      simpa only [Function.comp_apply,mul_zero] using (Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot).const_mul (Real.exp C)
    apply squeeze_zero (fun t ↦ mul_nonneg (Real.exp_pos _).le (cdf_nonneg _ _)) _ hlim
    intro t
    have h := Φ_le_exp_tilt (q₁ t) (-2*s) (by linarith)
    apply (mul_le_mul_of_nonneg_left h (Real.exp_pos _).le).trans_eq
    rw [← Real.exp_add,← Real.exp_add]
    congr 1
    dsimp [q₁,C]
    field_simp [hs.ne']
    ring
  have ht : Tendsto q₂ atTop atBot := by
    have h : Tendsto (fun t : ℝ ↦ (t-T)/s) atTop atTop :=
      affine_div_atTop T s hs
    convert tendsto_neg_atTop_atBot.comp h using 1
    funext t
    dsimp [q₂]
    ring
  have hlim : Tendsto F atTop (𝓝 0) := by
    simpa only [F,Φ,Function.comp_apply,sub_zero] using hTail.sub ((tendsto_cdf_atBot (gaussianReal 0 1)).comp ht)
  have hn (t : ℝ) (_ : t ∈ Ioi (0:ℝ)) : 0 ≤ Real.exp t*Φ (q₁ t) :=
    mul_nonneg (Real.exp_pos _).le (cdf_nonneg _ _)
  refine ⟨integrableOn_Ioi_deriv_of_nonneg' hf hn hlim,?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_nonneg' hf hn hlim]
  simp [F,q₁,q₂]

theorem gaussian_I2_integrable_and_integral (T s : ℝ) (hs : 0 < s) :
    IntegrableOn (fun t ↦ Φ ((T-t)/s)) (Ioi (0:ℝ)) ∧
      (∫ t in Ioi (0:ℝ), Φ ((T-t)/s)) = T*Φ (T/s)+s*φ (T/s) := by
  let q := fun t : ℝ ↦ (T-t)/s
  let F := fun t : ℝ ↦ (t-T)*Φ (q t)-s*φ (q t)
  have hf (t : ℝ) (_ : t ∈ Ici (0:ℝ)) : HasDerivAt F (Φ (q t)) t := by
    have hq : HasDerivAt q (-1/s) t := ((hasDerivAt_id t).const_sub T).div_const s
    have hd := (((hasDerivAt_id t).sub_const T).mul ((hasDerivAt_Φ (q t)).comp t hq)).sub
      (((hasDerivAt_φ (q t)).comp t hq).const_mul s)
    have he : 1*Φ (q t)+(t-T)*(φ (q t)*(-1/s))-s*(-q t*φ (q t)*(-1/s)) = Φ (q t) := by
      dsimp [q]
      field_simp [hs.ne']
      ring
    change HasDerivAt F (1*Φ (q t)+(t-T)*(φ (q t)*(-1/s))-s*(-q t*φ (q t)*(-1/s))) t at hd
    rwa [he] at hd
  have hPhi : Tendsto (fun t ↦ (t-T)*Φ (q t)) atTop (𝓝 0) := by
    let C := T+s^2/2
    have hx : Tendsto (fun t : ℝ ↦ t*Real.exp (-t)) atTop (𝓝 0) := by
      simpa only [pow_one] using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
    have hy : Tendsto (fun t : ℝ ↦ Real.exp C*((t-T)*Real.exp (-t))) atTop (𝓝 0) := by
      have he := hx.sub ((Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot).const_mul T)
      simpa only [mul_zero,sub_zero,Function.comp_apply,sub_mul] using he.const_mul (Real.exp C)
    apply squeeze_zero' _ _ hy
    · filter_upwards [eventually_ge_atTop T] with t ht
      exact mul_nonneg (sub_nonneg.mpr ht) (cdf_nonneg _ _)
    · filter_upwards [eventually_ge_atTop T] with t ht
      have H := Φ_le_exp_tilt (q t) (-s) (by linarith)
      apply (mul_le_mul_of_nonneg_left H (sub_nonneg.mpr ht)).trans_eq
      rw [← mul_assoc,mul_comm (Real.exp C),mul_assoc,← Real.exp_add]
      congr 2
      dsimp [q,C]
      field_simp [hs.ne']
      ring
  have hφ : Tendsto (fun t ↦ φ (q t)) atTop (𝓝 0) := by
    have hq : Tendsto (fun t : ℝ ↦ (t-T)/s) atTop atTop :=
      affine_div_atTop T s hs
    have hq2 := (tendsto_pow_atTop (α:=ℝ) (n:=2) (by norm_num)).comp hq
    have hArg := hq2.const_mul_atTop_of_neg (show (-1/2:ℝ)<0 by norm_num)
    have hx := (Real.tendsto_exp_atBot.comp hArg).const_mul ((Real.sqrt (2*Real.pi))⁻¹)
    rw [mul_zero] at hx
    apply hx.congr
    intro t
    simp only [Function.comp_apply,φ_exp]
    congr 2
    dsimp [q]
    ring
  have hlim : Tendsto F atTop (𝓝 0) := by
    simpa only [sub_zero,mul_zero] using hPhi.sub (hφ.const_mul s)
  have hn (t : ℝ) (_ : t ∈ Ioi (0:ℝ)) : 0 ≤ Φ (q t) := cdf_nonneg _ _
  refine ⟨integrableOn_Ioi_deriv_of_nonneg' hf hn hlim,?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_nonneg' hf hn hlim]
  simp [F,q]
  ring
end CubeBrownian
#print axioms CubeBrownian.gaussian_I1_integrable_and_integral
#print axioms CubeBrownian.gaussian_I2_integrable_and_integral
