import RetainedCount
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

open Set Finset
namespace CubeSqrtOverlap

/-- At most one period translate of a given defect's radius-two exclusion
band can intersect the actual physical interval [K/9,2K/9]. -/
theorem unique_defect_translate
    (K D x y : ℝ) (hK : 5 ≤ K) (hx : x ∈ Set.Icc (K/9) (2*K/9))
    (hy : y ∈ Set.Icc (K/9) (2*K/9))
    (i j : ℤ) (hi : |x-(D+(i:ℝ)*K)| ≤ 2) (hj : |y-(D+(j:ℝ)*K)| ≤ 2) :
    i = j := by
  have key (x y : ℝ) (i j : ℤ) (hx : x ∈ Set.Icc (K/9) (2*K/9))
      (hy : y ∈ Set.Icc (K/9) (2*K/9))
      (hi : |x-(D+(i:ℝ)*K)| ≤ 2) (hj : |y-(D+(j:ℝ)*K)| ≤ 2)
      (hij : i < j) : False := by
    have hab : (i:ℝ)+1 ≤ (j:ℝ) := by exact_mod_cast (show i+1 ≤ j by omega)
    have hm := mul_le_mul_of_nonneg_right hab (show 0 ≤ K by linarith only [hK])
    have hiL := (abs_le.mp hi).2
    have hjR := (abs_le.mp hj).1
    nlinarith only [hm,hiL,hjR,hx.1,hy.2,hK]
  rcases lt_trichotomy i j with h|h|h
  · exact (key x y i j hx hy hi hj h).elim
  · exact h
  · exact (key y x j i hy hx hj hi h).elim

/-- Count the paper's actual unsafe grid deletions using all node/defect
pairs and the one relevant periodic copy per defect. -/
theorem actual_unsafe_packet_deletions
    {I J : Type*} [Fintype I] [Fintype J]
    (S deleted : Finset ℕ) (hSub : deleted ⊆ S)
    (base : I → ℝ) (defect : J → ℝ) (K Δ : ℝ)
    (hK : 5 ≤ K) (hΔ : 0 < Δ)
    (hPhysical : ∀ i ∈ S, ∀ a, K*(base a+(i:ℝ)*Δ-1) ∈ Set.Icc (K/9) (2*K/9))
    (hBad : ∀ i ∈ deleted, ∃ (a : I) (j : J) (m : ℤ),
      |K*(base a+(i:ℝ)*Δ-1)-(defect j+(m:ℝ)*K)| ≤ 2) :
    (deleted.card:ℝ) ≤ (Fintype.card I:ℝ)*(Fintype.card J:ℝ)*((4/K)/Δ+1) := by
  classical
  let x (i : ℕ) (a : I) := K*(base a+(i:ℝ)*Δ-1)
  let bad (a : I) (j : J) := S.filter fun i ↦ ∃ m : ℤ, |x i a-(defect j+(m:ℝ)*K)| ≤ 2
  have hK0 : 0 < K := by linarith only [hK]
  apply packet_deletions_le deleted bad
  · intro i hi
    obtain ⟨a,j,m,hh⟩ := hBad i hi
    exact ⟨a,j,mem_filter.mpr ⟨hSub hi,⟨m,hh⟩⟩⟩
  · intro a j
    by_cases hne : (bad a j).Nonempty
    · obtain ⟨i₀,hi⟩ := hne
      obtain ⟨hi0S,m₀,hm₀⟩ := mem_filter.mp hi
      let c := defect j+(m₀:ℝ)*K
      let l := 1+(c-2)/K
      let h := 1+(c+2)/K
      have hWidth : h-l = 4/K := by
        dsimp [h,l]
        field_simp [hK0.ne'] <;> ring
      have hLH : l ≤ h := by
        have hz := div_nonneg (show (0:ℝ)≤4 by norm_num) hK0.le
        linarith only [hWidth,hz]
      have hBand (i : ℕ) (hi : i ∈ bad a j) : base a+(i:ℝ)*Δ ∈ Set.Icc l h := by
        obtain ⟨hiS,m,hm⟩ := mem_filter.mp hi
        have hmEq : m₀ = m := unique_defect_translate K (defect j) (x i₀ a) (x i a)
          hK (hPhysical i₀ hi0S a) (hPhysical i hiS a) m₀ m hm₀ hm
        subst m
        have hLo := (abs_le.mp hm).1
        have hUp := (abs_le.mp hm).2
        change l ≤ base a+(i:ℝ)*Δ ∧ base a+(i:ℝ)*Δ ≤ h
        constructor
        · unfold l
          have h := (div_le_iff₀ hK0).2 (show c-2 ≤ (base a+(i:ℝ)*Δ-1)*K by
            dsimp [x,c] at hLo ⊢
            nlinarith only [hLo])
          linarith only [h]
        · unfold h
          have hh := (le_div_iff₀ hK0).2 (show (base a+(i:ℝ)*Δ-1)*K ≤ c+2 by
            dsimp [x,c] at hUp ⊢
            nlinarith only [hUp])
          linarith only [hh]
      have hC := spacing_grid_band_card (bad a j) (base a) Δ l h hΔ hLH hBand
      rwa [hWidth] at hC
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne,Finset.card_empty,Nat.cast_zero]
      positivity

end CubeSqrtOverlap
#print axioms CubeSqrtOverlap.actual_unsafe_packet_deletions
