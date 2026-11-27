import ActualPeriodicSource
import SqrtLowerLiminf
import RetainedBonferroni

open MeasureTheory Set Filter Finset
open scoped Topology BigOperators ENNReal

namespace CenteredCubeSqrt

noncomputable def actualUnionCredit {n : ℕ} (h : ℝ) (R : Finset ℕ)
    (U : ℕ → Set (CenteredCube.Space n)) : ℝ :=
  Real.exp h * (CenteredCube.sqrtCellLaw n).real (⋃ i ∈ R, U i) / Real.sqrt (n:ℝ)

noncomputable def actualFirstCredit {n : ℕ} (h : ℝ) (R : Finset ℕ)
    (U : ℕ → Set (CenteredCube.Space n)) : ℝ :=
  (Real.exp h / Real.sqrt (n:ℝ)) *
    (∑ i ∈ R, (CenteredCube.sqrtCellLaw n).real (U i))

noncomputable def actualOverlapCredit {n : ℕ} (h : ℝ) (R : Finset ℕ)
    (U : ℕ → Set (CenteredCube.Space n)) : ℝ :=
  (Real.exp h / Real.sqrt (n:ℝ)) *
    (∑ i ∈ R, ∑ j ∈ R.filter (fun j => i < j), (CenteredCube.sqrtCellLaw n).real (U i∩U j))

theorem actual_packet_credits_bonferroni {n : ℕ} (h : ℝ) (R : Finset ℕ)
    (U : ℕ → Set (CenteredCube.Space n)) (hm : ∀ i, MeasurableSet (U i)) :
    actualFirstCredit h R U - actualOverlapCredit h R U ≤ actualUnionCredit h R U := by
  have H := CubeSqrtOverlap.retained_bonferroni_real (CenteredCube.sqrtCellLaw n) R U hm
  have g := mul_le_mul_of_nonneg_left H
    (div_nonneg (Real.exp_nonneg h) (Real.sqrt_nonneg (n:ℝ)))
  rw [mul_sub] at g
  convert g using 1 <;> simp [actualFirstCredit,actualOverlapCredit,actualUnionCredit]; ring

theorem actual_packet_credit_to_weakConstant {B K n : ℕ} [NeZero K]
    (f : ZMod K → Fin B) (M : ℕ) {p δ h : ℝ} (hn : 1 ≤ n) (hB : 0 < B) (hK : 2 ≤ K)
    (hp : 0 ≤ p) (hp1 : p < 1) (hδ : 0 < δ) (hst : δ < 1/((B:ℝ)*(K:ℝ)))
    (hc : (p/(K:ℝ)) * (9*(M:ℝ)) ≤ (1-p)/2)
    (R : Finset ℕ) (U : ℕ → Set (CenteredCube.Space n))
    (hm : ∀ i, MeasurableSet (U i))
    (hW : ∀ i∈R, ∀ x∈U i, ∃ L : ℝ, 0 < L ∧ L ≤ 2 ∧
      h < ∑ j, Real.log (1+actualWindowPerturbation f M p δ L (x j))) :
    ENNReal.ofReal (actualUnionCredit h R U *
      (1-1/(n:ℝ)^2)^n * Real.sqrt (n:ℝ)) ≤ CenteredCube.weakConstant n := by
  let E : Set (CenteredCube.Space n) := ⋃ i ∈ R, U i
  have hE : MeasurableSet E := by
    dsimp [E]
    exact MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun _ => hm i
  have hpoint : ∀ x∈E, ∃ L : ℝ, 0 < L ∧ L ≤ 2 ∧
      h < ∑ j, Real.log (1+actualWindowPerturbation f M p δ L (x j)) := by
    intro x hx
    obtain ⟨i,hi,hx⟩ := Set.mem_iUnion₂.1 hx
    exact hW i hi x hx
  have H := weakConstant_ge_actual_witness_iid_event f M hn hB hK hp hp1 hδ hst hc E hE hpoint
  have hh : Real.sqrt (n:ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by exact_mod_cast Nat.pos_of_ne_zero (by omega : n ≠ 0)))
  convert H using 1
  congr 1
  unfold actualUnionCredit E
  field_simp [hh]

/-- Combine the actual packet estimates and asymptotically lossless witness.
Inputs are eventually lower/upper credits, rather than exact first-sum limit. -/
theorem sqrt_eventually_of_actual_packet_credits
    (X S O : ℕ → ℝ) {A D b : ℝ} (hb : 0 < b) (hbA : b < A-D)
    (hSum : ∀ ε>0, ∀ᶠ n : ℕ in atTop, A-ε ≤ S n)
    (hOverlap : ∀ ε>0, ∀ᶠ n : ℕ in atTop, O n ≤ D+ε)
    (hBonf : ∀ᶠ n : ℕ in atTop, S n-O n ≤ X n)
    (hW : ∀ᶠ n : ℕ in atTop,
      ENNReal.ofReal (X n*(1-1/(n:ℝ)^2)^n*Real.sqrt (n:ℝ)) ≤ CenteredCube.weakConstant n) :
    ∀ᶠ n : ℕ in atTop, ENNReal.ofReal (b*Real.sqrt (n:ℝ)) ≤ CenteredCube.weakConstant n := by
  let g := (A-D-b)/4
  have hg : 0 < g := by dsimp [g]; linarith
  have hB : b < b+g := by linarith
  apply CenteredCube.sqrtWeakConstant_eventually_of_normalized_tail X hb hB _ hW
  filter_upwards [hSum g hg,hOverlap g hg,hBonf] with n ha hd hx
  dsimp [g] at *
  linarith

#print axioms actual_packet_credits_bonferroni
#print axioms actual_packet_credit_to_weakConstant
#print axioms sqrt_eventually_of_actual_packet_credits
end CenteredCubeSqrt
