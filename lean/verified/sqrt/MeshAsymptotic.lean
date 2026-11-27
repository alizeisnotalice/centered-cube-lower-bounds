import ActualMeshError

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace CubeBrownian

theorem mesh_error_uniform_bound {lo hi : ℝ} (hlo : 0 < lo) (hhi : 0 < hi)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ k ∈ Icc lo hi,
      let T := (n:ℝ)
      let b := hi/T^2
      let δ := (Real.sqrt T)⁻¹
      0 < n ∧ 8*b ≤ δ ∧
        ((1-Real.exp (-δ))*maxExpFormula (k*T) +
          8*(T^3)*(T^3+1)*Real.exp (δ-δ^2/(8*b)))/T < ε := by
  let δ (T : ℝ) := (Real.sqrt T)⁻¹
  have hd : Tendsto δ atTop (𝓝 0) := tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop
  have hC : Tendsto (fun T : ℝ ↦ (1-Real.exp (-(δ T)))*(hi+1)) atTop (𝓝 0) := by
    simpa only [Function.comp_apply,neg_zero,Real.exp_zero,sub_self,zero_mul] using
      ((tendsto_const_nhds (x:=(1:ℝ))).sub (Real.continuous_exp.continuousAt.tendsto.comp hd.neg)).mul_const (hi+1)
  have hP : Tendsto (fun T : ℝ ↦ 16*Real.exp 1*(T^5*Real.exp (-(1/(8*hi))*T))) atTop (𝓝 0) := by
    have hp := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 5 (1/(8*hi)) (by positivity)
    have hp' := hp.const_mul (16*Real.exp 1)
    rw [mul_zero] at hp'
    apply hp'.congr
    intro x
    have he : x^(5:ℝ) = x^(5:ℕ) := by simpa using Real.rpow_natCast x 5
    rw [he]
  have hε' : (0:ℝ)+0 < ε := by simpa only [zero_add] using hε
  have hTot := (hC.add hP).eventually_lt_const hε'
  have hUniform := maxExpFormula_div_uniform hlo hhi 1 zero_lt_one
  have hFar : ∀ᶠ T : ℝ in atTop, 1 ≤ T ∧ 8*hi ≤ T :=
    (eventually_ge_atTop (max 1 (8*hi))).mono
      (fun T h ↦ ⟨(le_max_left _ _).trans h,(le_max_right _ _).trans h⟩)
  have hn := tendsto_natCast_atTop_atTop (R:=ℝ)
  filter_upwards [hn.eventually hFar,hn.eventually hUniform,hn.eventually hTot] with n hn hF hSmall k hk
  dsimp only
  let T : ℝ := n
  let b := hi/T^2
  have h1 : 1 ≤ T := hn.1
  have ht : 0 < T := zero_lt_one.trans_le h1
  have htN : 0 < n := by
    exact_mod_cast (show (0:ℝ)<(n:ℝ) from ht)
  have hB : 0 < b := by dsimp [b]; positivity
  have hδ0 : 0 < δ T := by dsimp [δ]; positivity
  have hsq : (Real.sqrt T)^2 = T := Real.sq_sqrt ht.le
  have hS : 0 < Real.sqrt T := Real.sqrt_pos.mpr ht
  have hS1 : 1 ≤ Real.sqrt T := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt h1
  have hd1 : δ T ≤ 1 := inv_le_one_of_one_le₀ hS1
  have hSt : Real.sqrt T ≤ T := by
    nlinarith only [hsq,mul_nonneg hS.le (sub_nonneg.mpr hS1)]
  have h8 : 8*b ≤ δ T := by
    have hh : 8*hi*Real.sqrt T ≤ T^2 := by
      calc
        _ ≤ T*Real.sqrt T := mul_le_mul_of_nonneg_right hn.2 hS.le
        _ ≤ T*T := mul_le_mul_of_nonneg_left hSt ht.le
        _ = _ := by ring
    change 8*(hi/T^2) ≤ (Real.sqrt T)⁻¹
    have hq : 8*(hi/T^2) = (8*hi)/T^2 := by ring
    rw [hq,inv_eq_one_div]
    exact (div_le_div_iff₀ (sq_pos_of_pos ht) hS).2 (by simpa using hh)
  have hRatio : δ T^2/(8*b) = T/(8*hi) := by
    dsimp [δ,b]
    rw [inv_pow,hsq]
    field_simp
  have hK : maxExpFormula (k*T)/T ≤ hi+1 := by
    have h := hF k hk
    have h' := (abs_lt.mp h).2
    linarith only [h',hk.2]
  have hC0 : 0 ≤ 1-Real.exp (-(δ T)) := sub_nonneg.mpr
    (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hδ0.le))
  have hA : ((1-Real.exp (-(δ T)))*maxExpFormula (k*T))/T ≤
      (1-Real.exp (-(δ T)))*(hi+1) := by
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hK hC0
  have hBnd : (8*T^3*(T^3+1)*Real.exp (δ T-δ T^2/(8*b)))/T ≤
      16*Real.exp 1*(T^5*Real.exp (-(1/(8*hi))*T)) := by
    have hP₀ : 1 ≤ T^3 := by simpa using (pow_le_pow_left₀ zero_le_one h1 3)
    have hc : 8*T^3*(T^3+1)/T ≤ 16*T^5 := by
      have h₀ : T^3+1 ≤ 2*T^3 := by linarith only [hP₀]
      apply (div_le_iff₀ ht).2
      calc
        _ ≤ 8*T^3*(2*T^3) := mul_le_mul_of_nonneg_left h₀ (by positivity)
        _ = _ := by ring
    have he : Real.exp (δ T-δ T^2/(8*b)) ≤ Real.exp 1 * Real.exp (-(1/(8*hi))*T) := by
      rw [← Real.exp_add,hRatio]
      apply Real.exp_le_exp.mpr
      rw [show -(1/(8*hi))*T = -(T/(8*hi)) by ring]
      linarith only [hd1]
    calc
      _ = (8*T^3*(T^3+1)/T)*Real.exp (δ T-δ T^2/(8*b)) := by ring
      _ ≤ (16*T^5)*(Real.exp 1 * Real.exp (-(1/(8*hi))*T)) :=
        mul_le_mul hc he (Real.exp_pos _).le (by positivity)
      _ = _ := by ring
  refine ⟨htN,h8,?_⟩
  change ((1-Real.exp (-(δ T)))*maxExpFormula (k*T) +
    8*T^3*(T^3+1)*Real.exp (δ T-δ T^2/(8*b)))/T < ε
  rw [add_div]
  exact (add_le_add hA hBnd).trans_lt hSmall
end CubeBrownian
#print axioms CubeBrownian.mesh_error_uniform_bound
