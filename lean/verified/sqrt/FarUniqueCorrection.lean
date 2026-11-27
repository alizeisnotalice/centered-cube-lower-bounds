import ActualWalshCorrelation
import SqrtSafeCoarseLifts

namespace CenteredCubeSqrt
open MeasureTheory Set Classical MvPolynomial
open scoped BigOperators Interval
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
set_option maxHeartbeats 1700000

theorem actual_raw_far_unique_correction {b d : ℕ} [NeZero (2^d-1)] (hd : 0<d) (hb : 0<b)
    (g : (LabelField d)ˣ) (hg : orderOf g=2^d-1) {t : Fin b → LabelField d}
    (ht : LinearIndependent (ZMod 2) t) (hdim : 2*b≤d)
    (hS : MultiplicativeSidon {x : LabelField d | x ∈ labelSpace t ∧ x ≠ 0})
    (h0 : ∀ a, labelValue t a ≠ 0)
    (hp : Function.Injective (fun z : Sym2 (NonzeroBinary b) => eval t (symLabelProduct z)))
    (hadj : ∀ p q : UnequalLabels b,
      labelValue t p.1.1 * labelValue t q.1.2 ≠
        (g:LabelField d) * (labelValue t p.1.2 * labelValue t q.1.1))
    (k : ℤ) {θ : ℝ} (hθ : θ∈Icc (0:ℝ) 1)
    (hk : (k:ZMod (2^d-1)) ≠ 0) (hks : (k:ZMod (2^d-1))+1 ≠ 0) :
    let f := ordinalPhaseLabel hd g hg t
    let K := ((2^d-1:ℕ):ℝ)
    let q := (2:ℝ)^d
    let Q := unitRotatedInner (midpointError (2^b)) θ
    let Z := unitRotatedInner (cellPrimitive (labelCellMidpoint (0:Fin (2^b)))) θ
    ∃ C : ℝ,
       rawCorrelation f ((k:ℝ)+θ) = (q/K)*(Q+C)-Z/K ∧
       (C=0 ∨ ∃ a c : NonzeroBinary b, a ≠ c ∧
          (C=rawWalshLeft θ a c ∨ C=rawWalshRight θ a c)) := by
  classical
  let D := cyclicDefects hd g hg t
  let j₁ : ZMod (2^d-1) := k
  let j₂ := j₁+1
  let w₁ := rawCellMomentLeft (B:=2^b) θ
  let w₂ := rawCellMomentRight (B:=2^b) θ
  have H₁ : (phaseState hd g hg j₁ : LabelField d) ≠ 1 :=
    fun h => hk ((phaseState_eq_one_iff_zero hd g hg j₁).mp h)
  have H₂ : (phaseState hd g hg j₂ : LabelField d) ≠ 1 :=
    fun h => hks ((phaseState_eq_one_iff_zero hd g hg j₂).mp h)
  have R₁ (h : j₁∉D) := raw_regular_pair_sum hd g hg ht j₁ H₁ h hdim w₁
  have R₂ (h : j₂∉D) := raw_regular_pair_sum hd g hg ht j₂ H₂ h hdim w₂
  have E₁ (a c : NonzeroBinary b) (hm : labelValue t a = (phaseState hd g hg j₁ : LabelField d)*labelValue t c)
      (h : j₁∈D) := defective_ordinal_walsh_sum hd hb hdim g hg ht j₁ H₁ h hS a c hm w₁
  have E₂ (a c : NonzeroBinary b) (hm : labelValue t a = (phaseState hd g hg j₂ : LabelField d)*labelValue t c)
      (h : j₂∈D) := defective_ordinal_walsh_sum hd hb hdim g hg ht j₂ H₂ h hS a c hm w₂
  have corr := actual_raw_correlation_from_split_pair_laws hd g hg ht hdim k hθ
  by_cases h₁ : j₁∈D
  · have h₂ : j₂∉D := cyclicDefects_step_excluded hd g hg h0 hp hadj h₁
    obtain ⟨a,c,hac,hm⟩ := actual_walsh_match_of_defect hd g hg j₁ h₁
    refine ⟨rawWalshLeft θ a c, ?_, Or.inr ⟨a,c,hac,Or.inl rfl⟩⟩
    have p₁ := E₁ a c hm h₁
    have p₂ := R₂ h₂
    have hF := raw_left_walsh_factor hθ a c
    have H := corr (rawWalshLeft θ a c) 0 (by
      dsimp only at p₁ ⊢
      dsimp only [j₁,w₁] at p₁
      rw [p₁, ← hF]
      ring) (by simpa using p₂)
    simp only [add_zero] at H
    convert H using 1
    ring
  · by_cases h₂ : j₂∈D
    · obtain ⟨a,c,hac,hm⟩ := actual_walsh_match_of_defect hd g hg j₂ h₂
      refine ⟨rawWalshRight θ a c, ?_, Or.inr ⟨a,c,hac,Or.inr rfl⟩⟩
      have p₁ := R₁ h₁
      have p₂ := E₂ a c hm h₂
      have hF := raw_right_walsh_factor hθ a c
      have H := corr 0 (rawWalshRight θ a c) (by simpa using p₁) (by
        dsimp only at p₂ ⊢
        dsimp only [j₂,j₁,w₂] at p₂
        rw [p₂, ← hF]
        ring)
      simp only [add_zero] at H
      convert H using 1
      ring
    · refine ⟨0, ?_, Or.inl rfl⟩
      have H := corr 0 0 (by simpa using R₁ h₁) (by simpa using R₂ h₂)
      simp only [add_zero] at H
      convert H using 1
      ring

#print axioms actual_raw_far_unique_correction
end CenteredCubeSqrt
