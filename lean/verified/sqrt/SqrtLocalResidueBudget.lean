import SqrtPulseTrain
import SqrtLocalWindowArithmetic

namespace CenteredCubeSqrt

open scoped BigOperators
open Classical

noncomputable def physicalWindowResidues {B K : ℕ} [NeZero (B*K)]
    (v R shift : ℝ) : Finset (ZMod (B*K)) :=
  Finset.univ.filter fun r =>
    |((K:ℝ)*v)*((atomResidueLift shift r : ℝ)/((B:ℝ)*K)+shift)| ≤ R

theorem physicalWindowResidues_card_bound {B K : ℕ} [NeZero (B*K)]
    {v R shift : ℝ} {D : ℕ} (hB : 0 < B) (hK : 0 < K) (hv : 0 < v)
    (hR : 0 ≤ R) (hBv : (B:ℝ) ≤ 2*v) (hD : 2*R+1 ≤ D) :
    (physicalWindowResidues (B:=B) (K:=K) v R shift).card ≤ 2*D+1 := by
  let S := physicalWindowResidues (B:=B) (K:=K) v R shift
  let χ := atomResidueLift (N:=B*K) shift
  let x : ℝ := (B:ℝ)*K*(-shift)
  have hC : 0 < (K:ℝ)*v := by positivity
  calc
    S.card = (S.image χ).card := (Finset.card_image_of_injective S (atomResidueLift_injective shift)).symm
    _ ≤ (Finset.Icc (⌊x⌋-(D:ℤ)) (⌊x⌋+D)).card := by
      apply Finset.card_le_card
      intro ell hell
      obtain ⟨r,hr,h⟩ := Finset.mem_image.mp hell
      subst ell
      apply local_fine_window_contained (x:=x) hD
      unfold x χ
      apply local_fine_window_pullback (by positivity) (by positivity) hv hR hBv
      have h' := (Finset.mem_filter.mp hr).2
      rw [abs_mul, abs_of_pos hC] at h'
      apply (le_div_iff₀ hC).mpr
      simpa [mul_comm] using h'
    _ = 2*D+1 := padded_integer_window_card x D

/-- Finite-support summation in normalized coordinates; no scaling loss in
the off-diagonal window bound. -/
theorem physical_overlap_sum_budget {B K : ℕ} [NeZero (B*K)]
    {v eps T shift s t s' t' W : ℝ} {D : ℕ}
    (hB : 0 < B) (hK : 0 < K) (hv : 0 < v) (he : 0 < eps)
    (hT : 0 ≤ T) (hBv : (B:ℝ) ≤ 2*v) (hD : 2*(2*T+eps)+1 ≤ D)
    (hs : -T ≤ s) (hst : s ≤ t) (ht : t ≤ T)
    (hs' : -T ≤ s') (ht' : t' ≤ T)
    (wgt : ZMod (B*K) → ℝ) (hW : 0 ≤ W)
    (hw : ∀ r ∈ physicalWindowResidues (B:=B) (K:=K) v (2*T+eps) shift,
      0 ≤ wgt r ∧ wgt r ≤ W) :
    let kernel r := pulseOverlap eps s t s' t' (((K:ℝ)*v)*((atomResidueLift shift r : ℝ)/((B:ℝ)*K)+shift))
    0 ≤ (∑ r : ZMod (B*K), wgt r * kernel r) ∧
      (∑ r : ZMod (B*K), wgt r * kernel r) ≤ (2*(D:ℝ)+1)*W*(2*T) := by
  let S := physicalWindowResidues (B:=B) (K:=K) v (2*T+eps) shift
  let k : ZMod (B*K) → ℝ := fun r =>
    pulseOverlap eps s t s' t' (((K:ℝ)*v)*((atomResidueLift shift r : ℝ)/((B:ℝ)*K)+shift))
  change 0 ≤ (∑ r, wgt r*k r) ∧ (∑ r, wgt r*k r) ≤ _
  have hz (r : ZMod (B*K)) (hr : r ∉ S) : k r=0 := by
    dsimp [k]
    apply pulseOverlap_zero_far he hs ht hs' ht'
    simpa [S,physicalWindowResidues] using hr
  have e : (∑ r : ZMod (B*K), wgt r*k r) = ∑ r ∈ S, wgt r*k r := by
    symm
    apply Finset.sum_subset (Finset.subset_univ S)
    intro r _ hr
    rw [hz r hr,mul_zero]
  rw [e]
  have hcard := physicalWindowResidues_card_bound
    (B:=B) (K:=K) (shift:=shift) hB hK hv (show 0 ≤ 2*T+eps by linarith) hBv hD
  have hk0 (r : ZMod (B*K)) : 0 ≤ k r := (pulseOverlap_bounded he hst).1
  have hk1 (r : ZMod (B*K)) : k r ≤ 2*T :=
    (pulseOverlap_bounded he hst).2.trans (by linarith)
  constructor
  · exact Finset.sum_nonneg fun r hr => mul_nonneg (hw r hr).1 (hk0 r)
  · calc
      _ ≤ ∑ _r ∈ S, W*(2*T) := Finset.sum_le_sum fun r hr =>
        mul_le_mul (hw r hr).2 (hk1 r) (hk0 r) hW
      _ = (S.card:ℝ)*(W*(2*T)) := by simp [nsmul_eq_mul]
      _ ≤ (2*(D:ℝ)+1)*(W*(2*T)) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hcard)
          (mul_nonneg hW (by linarith))
      _ = _ := by ring

#print axioms physicalWindowResidues_card_bound
#print axioms physical_overlap_sum_budget

end CenteredCubeSqrt
