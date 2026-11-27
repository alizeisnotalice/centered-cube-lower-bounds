import Mathlib
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace CubeMD

noncomputable def saddleStrip (m q : ℝ) (k : ℕ) : Set ℝ :=
  Ico (m + (k : ℝ) / q) (m + ((k : ℝ) + 1) / q)

theorem saddleStrip_cover (m q : ℝ) (hq : 0 < q) :
    (⋃ k, saddleStrip m q k) = Ici m := by
  ext x
  simp only [mem_iUnion, mem_Ici, saddleStrip, mem_Ico]
  constructor
  · rintro ⟨k,hk,_⟩
    exact (le_add_of_nonneg_right (div_nonneg (Nat.cast_nonneg _) hq.le)).trans hk
  · intro hx
    let w := q * (x-m)
    have hw : 0 ≤ w := mul_nonneg hq.le (sub_nonneg.mpr hx)
    refine ⟨⌊w⌋₊, ?_, ?_⟩
    · have hk := Nat.floor_le hw
      have hh : ((⌊w⌋₊ : ℕ) : ℝ) / q ≤ x-m := (div_le_iff₀ hq).mpr (by simpa [w,mul_comm] using hk)
      linarith only [hh]
    · have hk := Nat.lt_floor_add_one w
      have hh : x-m < (((⌊w⌋₊ : ℕ) : ℝ) + 1) / q := (lt_div_iff₀ hq).mpr (by simpa [w,mul_comm] using hk)
      linarith only [hh]

theorem saddleStrip_pairwise_disjoint (m q : ℝ) (hq : 0 < q) :
    Pairwise (fun i j ↦ Disjoint (saddleStrip m q i) (saddleStrip m q j)) := by
  have hs (i j : ℕ) (h : i < j) : Disjoint (saddleStrip m q i) (saddleStrip m q j) := by
    refine Set.disjoint_left.2 ?_
    intro x hx hy
    have hh : (i : ℝ) + 1 ≤ j := by exact_mod_cast (Nat.succ_le_of_lt h)
    have h := add_le_add_right (div_le_div_of_nonneg_right hh hq.le) m
    exact (not_lt_of_ge (h.trans hy.1)) hx.2
  intro i j hij
  rcases lt_or_gt_of_ne hij with hh | hh
  · exact hs _ _ hh
  · exact (hs _ _ hh).symm

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ}

theorem tilted_tail_of_strip_masses [IsProbabilityMeasure μ]
    (hX : Measurable X) (q m A B : ℝ) (hq : 0 < q)
    (ht : Integrable (fun x ↦ Real.exp (q * X x)) μ)
    (hA : A ≤ (μ.tilted (q * X ·)).real (X ⁻¹' saddleStrip m q 0))
    (hB : ∀ k, (μ.tilted (q * X ·)).real (X ⁻¹' saddleStrip m q k) ≤ B) :
    Real.exp (-q * m + cgf X μ q - 1) * A ≤ μ.real (X ⁻¹' Ici m) ∧
    μ.real (X ⁻¹' Ici m) ≤ Real.exp (-q * m + cgf X μ q) * B / (1 - Real.exp (-1)) := by
  let E : ℕ → Set Ω := fun k ↦ X ⁻¹' saddleStrip m q k
  let ν := μ.tilted (q * X ·)
  let M := mgf X μ q
  have hM : 0 < M := mgf_pos ht
  have hEm (k : ℕ) : MeasurableSet (E k) := hX measurableSet_Ico
  have heq (k : ℕ) : ν.real (E k) = ∫ x in E k, Real.exp (q * X x) / M ∂μ := by
    rw [Measure.real, tilted_mul_apply_eq_ofReal_integral_mgf' (hEm k)]
    exact ENNReal.toReal_ofReal (integral_nonneg (fun _ ↦ div_nonneg (Real.exp_pos _).le hM.le))
  have hweights (k : ℕ) (x : Ω) (hx : x ∈ E k) :
      Real.exp (q*m+k) / M ≤ Real.exp (q * X x) / M ∧
      Real.exp (q * X x) / M ≤ Real.exp (q*m+k+1) / M := by
    have hlo := hx.1
    have hhi := hx.2
    change m + (k : ℝ) / q ≤ X x at hlo
    change X x < m + ((k : ℝ) + 1) / q at hhi
    have h1 : q*m+k ≤ q*X x := by
      have h := (div_le_iff₀ hq).mp (show (k : ℝ)/q ≤ X x-m by linarith only [hlo])
      linarith only [h]
    have h2 : q*X x ≤ q*m+k+1 := by
      have h := (lt_div_iff₀ hq).mp (show X x-m < ((k : ℝ)+1)/q by linarith only [hhi])
      linarith only [h]
    exact ⟨div_le_div_of_nonneg_right (Real.exp_le_exp.mpr h1) hM.le,
      div_le_div_of_nonneg_right (Real.exp_le_exp.mpr h2) hM.le⟩
  have hevent (k : ℕ) :
      μ.real (E k) * (Real.exp (q*m+k) / M) ≤ ν.real (E k) ∧
      ν.real (E k) ≤ μ.real (E k) * (Real.exp (q*m+k+1) / M) := by
    rw [heq]
    have hInt : IntegrableOn (fun x ↦ Real.exp (q * X x) / M) (E k) μ :=
      (ht.div_const M).integrableOn
    constructor
    · have h := setIntegral_mono_on (integrable_const (Real.exp (q*m+k) / M)) hInt
        (hEm k) (fun x hx ↦ (hweights k x hx).1)
      simpa only [setIntegral_const, smul_eq_mul] using h
    · have h := setIntegral_mono_on hInt (integrable_const (Real.exp (q*m+k+1) / M))
        (hEm k) (fun x hx ↦ (hweights k x hx).2)
      simpa only [setIntegral_const, smul_eq_mul] using h
  have hc : Real.exp (cgf X μ q) = M := Real.exp_log hM
  have hnormL : Real.exp (-q * m + cgf X μ q - 1) = (Real.exp (q*m+1) / M)⁻¹ := by
    rw [show -q*m + cgf X μ q - 1 = cgf X μ q - (q*m+1) by ring, Real.exp_sub, hc, inv_div]
  have hsub : E 0 ⊆ X ⁻¹' Ici m := by
    intro x hx
    have hx' := hx.1
    change m + (0 : ℝ) / q ≤ X x at hx'
    simpa using hx'
  constructor
  · rw [hnormL]
    have hpos : 0 < Real.exp (q*m+1) / M := div_pos (Real.exp_pos _) hM
    rw [← div_eq_inv_mul, div_le_iff₀ hpos]
    exact (hA.trans (by simpa [E] using (hevent 0).2)).trans
      (mul_le_mul_of_nonneg_right (measureReal_mono hsub) hpos.le)
  · let r := Real.exp (-1)
    let K := Real.exp (-q * m + cgf X μ q) * B
    have hrl : r < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
    have hr0 : 0 ≤ r := (Real.exp_pos _).le
    have hu (k : ℕ) : μ.real (E k) ≤ K * r^k := by
      have hpos : 0 < Real.exp (q*m+k) / M := div_pos (Real.exp_pos _) hM
      have hh := (le_div_iff₀ hpos).mpr ((hevent k).1.trans (hB k))
      have he : B / (Real.exp (q*m+k) / M) = K * r^k := by
        dsimp only [K,r]
        rw [Real.exp_add (q*m) (k:ℝ), Real.exp_add (-q*m) (cgf X μ q), hc, ← Real.exp_nat_mul,
          show (k:ℝ) * (-1) = -(k:ℝ) by ring, Real.exp_neg,
          show -q*m = -(q*m) by ring, Real.exp_neg]
        field_simp [hM.ne', (Real.exp_pos (q*m)).ne', (Real.exp_pos (k:ℝ)).ne'] <;> ring
      exact hh.trans_eq he
    have hdis : Pairwise (fun i j ↦ Disjoint (E i) (E j)) := by
      intro i j hij
      exact (saddleStrip_pairwise_disjoint m q hq hij).preimage X
    have hun : (⋃ k, E k) = X ⁻¹' Ici m := by
      simp only [E, ← preimage_iUnion, saddleStrip_cover m q hq]
    have hi : HasSum (fun k ↦ μ.real (E k)) (μ.real (X ⁻¹' Ici m)) := by
      have h := hasSum_integral_iUnion (μ := μ) (f := fun _ : Ω ↦ (1 : ℝ)) hEm hdis
        (integrable_const (μ := μ) (1 : ℝ)).integrableOn
      simpa only [setIntegral_const, smul_eq_mul, mul_one, hun] using h
    rw [← hi.tsum_eq]
    calc
      _ ≤ ∑' k : ℕ, K * r^k :=
        hi.summable.tsum_le_tsum hu ((summable_geometric_of_lt_one hr0 hrl).mul_left K)
      _ = _ := by rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hrl]; rfl

end CubeMD
#print axioms CubeMD.tilted_tail_of_strip_masses
