import FarRawBound
import SqrtActualSafeKernel
import SqrtKernelBudgetLimits

namespace CenteredCubeSqrt
open Set MeasureTheory MvPolynomial
open scoped BigOperators Interval
set_option maxHeartbeats 1500000
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem paperFarRawCap_eq_budget (b K : ℕ) :
    paperFarRawCap b K=paperFarRawBudget ((2:ℝ)^b) (K:ℝ) := rfl

theorem actualWitnessGram_exact_qualified_kernel {b d : ℕ} [NeZero (2^d-1)]
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
    let f := ordinalPhaseLabel hd g hg t
    let τ := K * |J-L|/2
    let κ := actualNormalizedGram f M δ L J
    ((-(1/2:ℝ)≤κ) ∧ (1/8≤τ → 1/5≤1-κ)) := by
  have ht1 : (phaseState hd g hg (1:ZMod (2^d-1)) : LabelField d) ≠ 1 := by
    rw [(cyclic_short_shift_values hd g hg).1]
    exact manuscriptShortShifts_ne_one (by rw [hg]; omega) 0
  have ht1' : (phaseState hd g hg (1:ZMod (2^d-1)) : LabelField d) ∉ labelRatioSet t :=
    (cyclicDefects_short_excluded hd g hg h0 hp hshort).1
  have hraw : ∀ z : ℝ, ((⌊z⌋:ℤ):ZMod (2^d-1)) ≠0 → (((⌊z⌋:ℤ)+1:ℤ):ZMod (2^d-1)) ≠0 →
      |rawCorrelation (ordinalPhaseLabel hd g hg t) z|≤paperFarRawBudget ((2:ℝ)^b) (((2^d-1:ℕ):ℝ)) := by
    rw [←paperFarRawCap_eq_budget]
    cases b with
    | zero => omega
    | succ a => exact actual_raw_far_cap hd g hg ht hdim (actual_labelSpace_Sidon hp) h0 hp hadj
  exact actualWitnessGram_uniform_safe_kernel hd g hg t ht hdim M hM hM0 hδ hδ1 hδB hKδ hK hL hJ
    hSafeL hSafeJ ht1 ht1' hraw hQ hE hEN hV

#print axioms actualWitnessGram_exact_qualified_kernel
end CenteredCubeSqrt
