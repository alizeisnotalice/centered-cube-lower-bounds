import CanonicalFiniteGrid
import Mathlib.Order.Filter.Finite

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology RealInnerProductSpace
namespace CubeBrownian

set_option maxHeartbeats 1800000
set_option linter.style.haveILetI false

theorem canonical_finite_grid_uniform
    {H ι α : Type*} {l : Filter α} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [Fintype ι] [Nonempty ι]
    (f : α → ι → H) (g : ι → H) (hf : ∀ i, Tendsto (fun n ↦ f n i) l (𝓝 (g i)))
    (K : ℝ≥0) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : α in l, ∀ k : ℝ≥0, k ≤ K →
      |canonicalFiniteGridExp (f n) k-canonicalFiniteGridExp g k| < ε := by
  classical
  let R : ℝ := 1 + ∑ i, ‖g i‖
  let N : ℝ := Fintype.card ι
  let M := Real.exp ((K:ℝ)*R^2)
  let p := 1+4*N*M/ε
  let c (n : α) (i : ι) :=
    (K:ℝ)*‖f n i-g i‖^2 +
    ((K:ℝ)/2)^2*(‖f n i‖^2-‖g i‖^2)^2
  have hK : 0 ≤ (K:ℝ) := NNReal.coe_nonneg _
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hM : 0 < M := Real.exp_pos _
  have hp : 0 < p := by dsimp [p]; positivity
  have hbase i : ‖g i‖ ≤ R-1 := by
    have hs := Finset.single_le_sum (f:=fun i ↦ ‖g i‖)
      (fun _ _ ↦ norm_nonneg _) (Finset.mem_univ i)
    dsimp [R]
    linarith
  have hfg : ∀ᶠ n in l, ∀ i, ‖f n i‖ ≤ R := by
    apply eventually_all.mpr
    intro i
    exact ((hf i).norm.eventually_lt_const (by linarith only [hbase i])).mono (fun _ h ↦ h.le)
  have hc i : Tendsto (fun n ↦ c n i) l (𝓝 0) := by
    have ha := (((hf i).sub (tendsto_const_nhds : Tendsto (fun _ : α ↦ g i) l (𝓝 (g i)))).norm.pow 2).const_mul (K:ℝ)
    have hb := ((((hf i).norm.pow 2).sub (tendsto_const_nhds : Tendsto (fun _ : α ↦ ‖g i‖^2) l (𝓝 (‖g i‖^2)))).pow 2).const_mul (((K:ℝ)/2)^2)
    simpa [c]
      using ha.add hb
  let e := ε / (p*(N+1))
  have he : 0 < e := by dsimp [e]; positivity
  have hsmall : ∀ᶠ n in l, ∀ i, c n i ≤ e := by
    apply eventually_all.mpr
    intro i
    exact ((hc i).eventually_lt_const he).mono (fun _ h ↦ h.le)
  have hB : (p/2)*(N*e) ≤ ε/2 := by
    change p/2*(N*(ε/(p*(N+1)))) ≤ _
    have hnp : 0 < N+1 := by linarith
    have hc : p/2*(N*(ε/(p*(N+1)))) = (ε/2)*(N/(N+1)) := by field_simp
    rw [hc]
    exact mul_le_of_le_one_right (by positivity) (div_le_one_of_le₀ (by linarith) hnp.le)
  have hlast : (2*N*M)/p < ε/2 := by
    apply (div_lt_iff₀ hp).2
    have h : (ε/2)*p = ε/2+2*N*M := by dsimp [p]; field_simp; ring
    rw [h]
    linarith
  filter_upwards [hfg,hsmall] with n hn hcN k hk
  let S := Submodule.span ℝ (Set.range (f n) ∪ Set.range g)
  letI : MeasurableSpace S := borel _
  letI : BorelSpace S := ⟨rfl⟩
  letI : FiniteDimensional ℝ S := FiniteDimensional.span_of_finite ℝ
    ((Set.finite_range (f n)).union (Set.finite_range g))
  let F (i : ι) : S := ⟨f n i,Submodule.subset_span (Or.inl (Set.mem_range_self i))⟩
  let G (i : ι) : S := ⟨g i,Submodule.subset_span (Or.inr (Set.mem_range_self i))⟩
  let μ := stdGaussian S
  let W := pairedSpanIsonormal S
  have hmW (x : S) := measurable_pairedSpanIsonormal x
  have hW (x : S) := pairedSpanIsonormal_hasLaw x
  have EF := finite_isonormal_expMax_eq_canonical μ W hW F (f n) (fun _ _ => rfl) k
  have EG := finite_isonormal_expMax_eq_canonical μ W hW G g (fun _ _ => rfl) k
  rw [←EF,←EG]
  let X i := isoScore W k (F i)
  let Y i := isoScore W k (G i)
  have hkR : (k:ℝ) ≤ (K:ℝ) := by exact_mod_cast hk
  have hk0 : 0 ≤ (k:ℝ) := NNReal.coe_nonneg _
  have hMeas (x : S) : Measurable (isoScore W k x) :=
    (measurable_const.mul (hmW x)).sub measurable_const
  have hOne (x : S) : Integrable (fun w ↦ Real.exp (isoScore W k x w)) μ := by
    have hl := isoScore_hasLaw μ W hW k x
    apply (integrable_map_measure Real.measurable_exp.aestronglyMeasurable hl.aemeasurable).mp
    rw [hl.map_eq]
    simpa only [one_mul] using
      (integrable_exp_mul_gaussianReal (μ:=-(isoVar k x:ℝ)/2) (v:=isoVar k x) 1)
  have hTwo (x : S) := gaussian_half_variance_exp_second_moment (isoScore_hasLaw μ W hW k x)
  have hD i := isoScore_coupled_second_moment μ W hW k (F i) (G i)
  have hExp (x : S) (hx : ‖x‖ ≤ R) :
      (∫ w, Real.exp (2*isoScore W k x w) ∂μ) ≤ M := by
    rw [(hTwo x).2]
    apply Real.exp_le_exp.mpr
    change (k:ℝ)*‖x‖^2 ≤ (K:ℝ)*R^2
    exact mul_le_mul hkR (pow_le_pow_left₀ (norm_nonneg _) hx 2) (sq_nonneg _) hK
  have hΔ (i : ι) : (∫ w, (X i w-Y i w)^2 ∂μ) ≤ c n i := by
    have h := (hD i).2
    change (∫ w, (X i w-Y i w)^2 ∂μ) = _ at h
    rw [h]
    change (k:ℝ)*‖f n i-g i‖^2 + (((k:ℝ)*‖f n i‖^2-(k:ℝ)*‖g i‖^2)/2)^2 ≤ _
    rw [show (((k:ℝ)*‖f n i‖^2-(k:ℝ)*‖g i‖^2)/2)^2 =
      ((k:ℝ)/2)^2*(‖f n i‖^2-‖g i‖^2)^2 by ring]
    exact add_le_add (mul_le_mul_of_nonneg_right hkR (sq_nonneg _))
      (mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (by positivity) (div_le_div_of_nonneg_right hkR (by norm_num)) 2)
        (sq_nonneg _))
  have hsumD : (∑ i, ∫ w, (X i w-Y i w)^2 ∂μ) ≤ N*e := by
    simpa [N] using (Finset.sum_le_sum (s:=Finset.univ) (fun i _ ↦ (hΔ i).trans (hcN i)))
  have hsumX : (∑ i, ∫ w, Real.exp (2*X i w) ∂μ) ≤ N*M := by
    simpa [N] using (Finset.sum_le_sum (s:=Finset.univ) (fun i _ ↦ hExp (F i) (hn i)))
  have hlimit (i : ι) : ‖g i‖ ≤ R := (hbase i).trans (sub_le_self _ zero_le_one)
  have hsumY : (∑ i, ∫ w, Real.exp (2*Y i w) ∂μ) ≤ N*M := by
    simpa [N] using (Finset.sum_le_sum (s:=Finset.univ)
      (fun i _ ↦ hExp (G i) (hlimit i)))
  have H := expMax_expectation_young μ X Y p hp (fun i ↦ hMeas _) (fun i ↦ hMeas _)
    (fun i ↦ hOne _) (fun i ↦ hOne _)
    (fun i ↦ (hTwo (F i)).1) (fun i ↦ (hTwo (G i)).1) (fun i ↦ (hD i).1)
  apply H.trans_lt
  apply lt_of_le_of_lt (add_le_add (mul_le_mul_of_nonneg_left hsumD (by positivity))
    (div_le_div_of_nonneg_right (add_le_add hsumX hsumY) hp.le))
  have heq : (N*M+N*M)/p = (2*N*M)/p := by ring
  rw [heq]
  linarith only [hB,hlast]

#print axioms canonical_finite_grid_uniform
end CubeBrownian
