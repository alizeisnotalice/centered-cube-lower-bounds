import PairUniformPrefactor
import PairFixedEnvelope

open MeasureTheory ProbabilityTheory Set Filter CubeBrownian
open scoped NNReal ENNReal Topology ProbabilityTheory
namespace CubeSqrtPair

/-- Exact finite actual-source pair bounds in the variance/correlation
notation of the paper. The remaining geometric input is only the actual
entrywise variances and kernel correlation for the source. -/
theorem paper_allpairs_finite
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (d e : Ω → ℝ) (hmd : Measurable d) (hme : Measurable e)
    (a : ℝ) (ha0 : 0 ≤ a) (ha : a ≤ 1/8)
    (hd : ∀ w, |d w| ≤ a) (he : ∀ w, |e w| ≤ a)
    (hd0 : ∫ w, d w ∂P = 0) (he0 : ∫ w, e w ∂P = 0)
    {n : ℕ} (hn : 0 < n) (h u v C qY qZ κ : ℝ) (hu : 0 < u) (huv : u^2=v)
    (hvc : v/2 ≤ v-C) (hκlo : -1/2 ≤ κ) (hκhi : κ ≤ 1)
    (hqY : qY = (n:ℝ)*(∫ w, (d w)^2 ∂P))
    (hqZ : qZ = (n:ℝ)*(∫ w, (e w)^2 ∂P))
    (hYlo : v-C ≤ qY) (hZlo : v-C ≤ qZ)
    (hCov : (n:ℝ)*cov[d,e;P] = Real.sqrt qY*Real.sqrt qZ*κ) :
    let L := fun w ↦ Real.log (1+d w)
    let J := fun w ↦ Real.log (1+e w)
    let H := avgAffinity P L J
    let A : Set (Fin n → Ω) := {x | h < ∑ i, L (x i)}
    let B : Set (Fin n → Ω) := {x | h < ∑ i, J (x i)}
    u*Real.exp h*(Measure.pi (fun _ : Fin n ↦ P)).real (A∩B) ≤ (12*(φ 0+30))*H^n ∧
      H^n ≤ Real.exp (-((v-C)*(1-κ)/(4*(1+a)))) := by
  dsimp only
  let A := ∫ w, (d w)^2 ∂P
  let B := ∫ w, (e w)^2 ∂P
  have hA : 0 ≤ A := integral_nonneg (fun _ ↦ sq_nonneg _)
  have hB : 0 ≤ B := integral_nonneg (fun _ ↦ sq_nonneg _)
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  have hv : 0 ≤ v := huv ▸ sq_nonneg u
  have hExpand : Real.sqrt qY*Real.sqrt qZ*κ = (n:ℝ)*(Real.sqrt A*Real.sqrt B*κ) := by
    rw [hqY,hqZ]
    change Real.sqrt ((n:ℝ)*A)*Real.sqrt ((n:ℝ)*B)*κ = _
    rw [Real.sqrt_mul hnR.le,Real.sqrt_mul hnR.le]
    calc
      _ = (Real.sqrt (n:ℝ))^2*(Real.sqrt A*Real.sqrt B*κ) := by ring
      _ = _ := by rw [Real.sq_sqrt hnR.le]
  have hC : cov[d,e;P] = Real.sqrt A*Real.sqrt B*κ := by
    rw [hExpand] at hCov
    exact mul_left_cancel₀ hnR.ne' hCov
  have hClo : -Real.sqrt A*Real.sqrt B/2 ≤ cov[d,e;P] := by
    have H := mul_le_mul_of_nonneg_left hκlo
      (mul_nonneg (Real.sqrt_nonneg A) (Real.sqrt_nonneg B))
    rw [hC]
    calc
      _ = (Real.sqrt A*Real.sqrt B)*(-1/2) := by ring
      _ ≤ _ := H
  have hqYL : u^2/2 ≤ (n:ℝ)*A := by change qY = (n:ℝ)*A at hqY; rw [huv,← hqY]; exact hvc.trans hYlo
  have hqZL : u^2/2 ≤ (n:ℝ)*B := by change qZ = (n:ℝ)*B at hqZ; rw [huv,← hqZ]; exact hvc.trans hZlo
  exact ⟨actual_pair_uniform_prefactor P d e hmd hme a ha0 ha hd he hd0 he0 hn h u hu hqYL hqZL hClo,
    kernel_affinity_exp_bound P d e hmd hme a ha0 (ha.trans (by norm_num)) hd he hd0 he0 n
      qY qZ v C κ hκhi ((by positivity : 0 ≤ v/2).trans hvc) hqY hqZ hYlo hZlo hCov⟩

end CubeSqrtPair
#print axioms CubeSqrtPair.paper_allpairs_finite
