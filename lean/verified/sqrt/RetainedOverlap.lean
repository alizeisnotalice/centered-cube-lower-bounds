import RetainedNear
import RetainedReindex
import RetainedBonferroni

open Set Finset MeasureTheory
namespace CubeSqrtOverlap

/-- Normalized overlap estimate for the exact retained packets and all their
nodes. A uniform near envelope and a uniform non-near node estimate suffice. -/
theorem retained_packet_overlap_normalized
    {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    (μ : Measure Ω) [IsFiniteMeasure μ] (B : ℕ) (R : Finset ℕ)
    (hR : R ⊆ range B) (hRe : R.Nonempty)
    (E : ℕ → I → Set Ω) (lam P T G c C F : ℝ)
    (hlam : 0 ≤ lam) (hP : 0 < P) (hc : 0 < c) (hC : 0 ≤ C) (hF : 0 ≤ F)
    (hspacing : T+G ≤ P)
    (offset : I → ℝ) (hL : ∀ a, 0 ≤ offset a) (hU : ∀ a, offset a ≤ T)
    (near : ℕ → ℕ → I → I → Prop)
    (hNear : ∀ i ∈ R, ∀ j ∈ R, i < j → ∀ a b, near i j a b →
      lam*μ.real (E i a∩ E j b) ≤
        C*Real.exp (-c*((j:ℝ)*P+offset b-((i:ℝ)*P+offset a))))
    (hFar : ∀ i ∈ R, ∀ j ∈ R, i < j → ∀ a b, ¬near i j a b →
      lam*μ.real (E i a∩E j b) ≤ F) :
    let U (i : ℕ) := ⋃ a, E i a
    lam*(∑ i ∈ R,∑ j ∈ R.filter (fun j ↦ i < j), μ.real (U i∩U j))/(R.card:ℝ) ≤
      (Fintype.card I:ℝ)^2*(C*Real.exp (-c*G)/(1-Real.exp (-c*P))+(B:ℝ)*F) := by
  classical
  dsimp only
  let U (i : ℕ) := ⋃ a, E i a
  let A (i j : ℕ) (a b : I) := lam*μ.real (E i a∩E j b)
  let W (i k : ℕ) (a b : I) := if i+k+1 ∈ R then A i (i+k+1) a b else 0
  let Wn (i k : ℕ) (a b : I) := if near i (i+k+1) a b then W i k a b else 0
  let Wf (i k : ℕ) (a b : I) := if near i (i+k+1) a b then 0 else W i k a b
  have hWn : ∀ i ∈ R, ∀ k ∈ range (B-i-1), ∀ a b,
      Wn i k a b ≤ C*Real.exp (-c*(((i+k+1:ℕ):ℝ)*P+offset b-((i:ℝ)*P+offset a))) := by
    intro i hi k hk a b
    by_cases hj : i+k+1 ∈ R <;> by_cases hn : near i (i+k+1) a b
    · simpa [Wn,W,A,hj,hn] using hNear i hi (i+k+1) hj (by omega) a b hn
    all_goals simp [Wn,W,hj,hn,mul_nonneg hC (Real.exp_pos _).le]
  have hWf : ∀ i ∈ R, ∀ k ∈ range (B-i-1), ∀ a b, Wf i k a b ≤ F := by
    intro i hi k hk a b
    by_cases hj : i+k+1 ∈ R <;> by_cases hn : near i (i+k+1) a b
    · simpa [Wf,hn] using hF
    · simpa [Wf,W,A,hj,hn] using hFar i hi (i+k+1) hj (by omega) a b hn
    all_goals simpa [Wf,W,hj,hn] using hF
  have hN := retained_near_total B R P T G c C hP hc hC hspacing offset offset hL hU hL Wn hWn
  have hM := retained_far_total B R F hF Wf hWf
  have hSplit (i k : ℕ) (a b : I) : W i k a b = Wn i k a b+Wf i k a b := by
    by_cases hh : near i (i+k+1) a b <;> simp [Wn,Wf,hh]
  have hEq (i : ℕ) : (∑ j ∈ R.filter (fun j ↦ i<j), ∑ a, ∑ b, A i j a b) =
      ∑ k ∈ range (B-i-1), ∑ a, ∑ b, W i k a b := by
    rw [retained_row_as_original_gaps B R hR i (fun j ↦ ∑ a, ∑ b, A i j a b)]
    apply sum_congr rfl
    intro k _
    by_cases hh : i+k+1 ∈ R <;> simp [W,hh]
  have hPacket :
      lam*(∑ i ∈ R,∑ j ∈ R.filter (fun j ↦ i<j), μ.real (U i∩U j)) ≤
        ∑ i ∈ R, ∑ k ∈ range (B-i-1), ∑ a : I, ∑ b : I, W i k a b := by
    simp_rw [mul_sum, ←hEq]
    apply sum_le_sum
    intro i hi
    apply sum_le_sum
    intro j hj
    have hh := mul_le_mul_of_nonneg_left (packet_intersection_le_double_node_sum μ (E i) (E j)) hlam
    simpa only [U,mul_sum,A] using hh
  have hJ : 0 < (R.card:ℝ) := by exact_mod_cast R.card_pos.mpr hRe
  apply (div_le_iff₀ hJ).2
  refine hPacket.trans ?_
  simp_rw [hSplit,sum_add_distrib]
  have hB := add_le_add hN hM
  refine hB.trans_eq ?_
  ring

end CubeSqrtOverlap
#print axioms CubeSqrtOverlap.retained_packet_overlap_normalized
