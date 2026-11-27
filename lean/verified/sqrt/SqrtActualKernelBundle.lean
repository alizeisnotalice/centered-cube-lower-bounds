import SqrtActualKernelClosed

namespace CenteredCubeSqrt
open Set MeasureTheory MvPolynomial
open scoped BigOperators Interval
set_option maxHeartbeats 1500000
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem actualWitnessGram_complete_kernel_lemma {b d : ℕ} [NeZero (2^d-1)]
    (hb : 0<b) (hd : 0<d) (g : (LabelField d)ˣ) (hg : orderOf g=2^d-1) (t : Fin b → LabelField d)
    (ht : LinearIndependent (ZMod 2) t) (hdim : 2*b≤d)
    (h0 : ∀ a, labelValue t a ≠ 0)
    (hp : Function.Injective (fun z : Sym2 (NonzeroBinary b) => eval t (symLabelProduct z)))
    (hadj : ∀ p q : UnequalLabels b,
      labelValue t p.1.1 * labelValue t q.1.2 ≠
        (g:LabelField d) * (labelValue t p.1.2 * labelValue t q.1.1))
    (hshort : ∀ (p : UnequalLabels b) (j : Fin 4),
      labelValue t p.1.1 ≠ manuscriptShortShifts g j * labelValue t p.1.2)
    (M : ℕ) (hM : M<2^d-1) (hM0 : 0<M)
    {δ L J : ℝ} (hδ : 0<δ) (hδ1 : δ<1)
    (hδB : δ<1/((((2^b:ℕ):ℝ))*(((2^d-1:ℕ):ℝ))))
    (hKδ : (((2^d-1:ℕ):ℝ))*δ≤1)
    (hK : 18≤(2^d-1:ℕ)) (hL : L∈Icc (10/9:ℝ) (11/9)) (hJ : J∈Icc (10/9:ℝ) (11/9))
    (hSafeL : actualSafeLifts hd g hg t L) (hSafeJ : actualSafeLifts hd g hg t J)
    (hQ : paperFarRawBudget ((2:ℝ)^b) (((2^d-1:ℕ):ℝ))≤21/500)
    (hE :
      let K := ((2^d-1:ℕ):ℝ)
      let B := (2:ℝ)^b
      (2/3)*K*δ+manuscriptCrossError B K M≤1/1000)
    (hEN :
      let K := ((2^d-1:ℕ):ℝ)
      let B := (2:ℝ)^b
      2/(3*B^2)+2/K+(2/3)*K*δ+manuscriptCrossError B K M≤1/1000)
    (hV :
      let K := ((2^d-1:ℕ):ℝ)
      let B := (2:ℝ)^b
      19/50≤100/261-(48/(29*(M:ℝ)^3))/3-
        (1/(3*B^2)+2/K+(2/3)*K*δ+manuscriptCrossError B K M)) :
    let K := ((2^d-1:ℕ):ℝ)
    let B := (2:ℝ)^b
    let f := ordinalPhaseLabel hd g hg t
    let EN := 2/(3*B^2)+2/K+(2/3)*K*δ+manuscriptCrossError B K M
    let AD := 1/(3*B^2)+2/K+(2/3)*K*δ+manuscriptCrossError B K M
    let TM := 48/(29*(M:ℝ)^3)
    let V := 100/261-TM/3-AD
    let R := (TM+3*AD)/(100/87)
    let τ := K * |J-L|/2
    let κ := actualNormalizedGram f M δ L J
    ((V≤actualWitnessGram f M δ L L ∧
      |actualWitnessGram f M δ L L/((27/29)*L^2/3)-1|≤R) ∧
    (V≤actualWitnessGram f M δ J J ∧
      |actualWitnessGram f M δ J J/((27/29)*J^2/3)-1|≤R) ∧
    (τ≤1/8 → (174/121)*τ-8*EN≤1-κ) ∧
    (1/8≤τ → τ≤1 → 14703/61952-8*EN≤1-κ) ∧
    -(1/2:ℝ)≤κ ∧ (1/8≤τ → 1/5≤1-κ)) := by
  let K := ((2^d-1:ℕ):ℝ)
  let B := (2:ℝ)^b
  let f := ordinalPhaseLabel hd g hg t
  let AD := 1/(3*B^2)+2/K+(2/3)*K*δ+manuscriptCrossError B K M
  let EN := 2/(3*B^2)+2/K+(2/3)*K*δ+manuscriptCrossError B K M
  let TM := 48/(29*(M:ℝ)^3)
  let V := 100/261-TM/3-AD
  let R := (TM+3*AD)/(100/87)
  have hquarter : 1/4≤V := by
    have h : 19/50≤V := hV
    linarith
  have ht1 : (phaseState hd g hg (1:ZMod (2^d-1)) : LabelField d) ≠ 1 := by
    rw [(cyclic_short_shift_values hd g hg).1]
    exact manuscriptShortShifts_ne_one (by rw [hg]; omega) 0
  have ht1' : (phaseState hd g hg (1:ZMod (2^d-1)) : LabelField d) ∉ labelRatioSet t :=
    (cyclicDefects_short_excluded hd g hg h0 hp hshort).1
  have diag (x : ℝ) (hx : x∈Icc (10/9:ℝ) (11/9)) (hs : actualSafeLifts hd g hg t x) :
      V≤actualWitnessGram f M δ x x ∧
        |actualWitnessGram f M δ x x/((27/29)*x^2/3)-1|≤R := by
    have H : |actualWitnessGram f M δ x x-finitePlateau M x/3|≤AD :=
      actualWitnessGram_diagonal_error hd g hg t ht hdim M hM hδ hδ1 hδB hKδ hK hx hs
    exact paper_kernel_diagonal_assembly hx (paper_plateau_finite_tail hx hM0) H
  have near (P U : ℝ) (hP : P∈Icc (10/9:ℝ) (11/9)) (hU : U∈Icc (10/9:ℝ) (11/9))
      (hSP : actualSafeLifts hd g hg t P) (hSU : actualSafeLifts hd g hg t U) (hPU : P≤U) :
      let τ := K * |U-P|/2
      let κ := actualNormalizedGram f M δ P U
      ((τ≤1/8 → (174/121)*τ-8*EN≤1-κ) ∧
       (1/8≤τ → τ≤1 → 14703/61952-8*EN≤1-κ)) := by
    let τ := K*(U-P)/2
    have hτ0 : 0≤τ := by dsimp [τ,K]; positivity
    dsimp only
    rw [abs_of_nonneg (sub_nonneg.mpr hPU)]
    change (τ≤1/8 → (174/121)*τ-8*EN≤1-actualNormalizedGram f M δ P U) ∧
      (1/8≤τ → τ≤1 → 14703/61952-8*EN≤1-actualNormalizedGram f M δ P U)
    constructor
    · intro hh
      have H : τ∈Icc (0:ℝ) 1 := ⟨hτ0,by linarith⟩
      exact (actualWitnessGram_normalized_near_gaps hd g hg t ht hdim M hM hM0 hδ hδ1 hδB
        hKδ hK hP hU hSP hSU H ht1 ht1' hquarter).1 hh
    · intro hh hh'
      have H : τ∈Icc (0:ℝ) 1 := ⟨hτ0,hh'⟩
      exact (actualWitnessGram_normalized_near_gaps hd g hg t ht hdim M hM hM0 hδ hδ1 hδB
        hKδ hK hP hU hSP hSU H ht1 ht1' hquarter).2 hh
  have uniform := actualWitnessGram_exact_qualified_kernel hb hd g hg t ht hdim h0 hp hadj hshort
    M hM hM0 hδ hδ1 hδB hKδ hK hL hJ hSafeL hSafeJ hQ hE hEN hV
  have H : (K * |J-L|/2≤1/8 → (174/121)*(K * |J-L|/2)-8*EN≤1-actualNormalizedGram f M δ L J) ∧
      (1/8≤K * |J-L|/2 → K * |J-L|/2≤1 → 14703/61952-8*EN≤1-actualNormalizedGram f M δ L J) := by
    rcases le_total L J with hh|hh
    · exact near L J hL hJ hSafeL hSafeJ hh
    · have W := near J L hJ hL hSafeJ hSafeL hh
      dsimp only at W
      rw [abs_sub_comm L J,actualNormalizedGram_comm f M δ J L] at W
      exact W
  exact ⟨diag L hL hSafeL,diag J hJ hSafeJ,H.1,H.2,uniform.1,uniform.2⟩

#print axioms actualWitnessGram_complete_kernel_lemma
end CenteredCubeSqrt
