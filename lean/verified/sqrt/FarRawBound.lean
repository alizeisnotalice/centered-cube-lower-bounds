import WalshShiftCauchy
import SqrtRawDiagonalSafe

namespace CenteredCubeSqrt
open MeasureTheory Set Classical MvPolynomial
open scoped Interval BigOperators
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

noncomputable def paperFarRawCap (b K : ℕ) : ℝ :=
  paperWalshQ b+1/(12*((2:ℝ)^b)^2)+1/(2*(K:ℝ))

theorem paperWalshQ_one_eighth (b : ℕ) : paperWalshQ (b+1) ≤ 1/8 := by
  have h2 : 2≤(2:ℝ)^(b+1) := by
    rw [pow_succ]
    have h := one_le_pow₀ (by norm_num : 1≤(2:ℝ)) (n:=b)
    linarith
  have h4 := pow_le_pow_left₀ (by norm_num : 0≤(2:ℝ)) h2 2
  have h : 1/(6*((2:ℝ)^(b+1))^2) ≤ 1/24 := by
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  have hu : upperWalshEnergy (b+1) ≤ 1/8 := by unfold upperWalshEnergy; linarith
  have hl : lowerWalshEnergy (b+1) ≤ 1/8 := by unfold lowerWalshEnergy; linarith
  have hL : 0≤lowerWalshEnergy (b+1) := by unfold lowerWalshEnergy; positivity
  have e := mul_le_mul hu hl hL (by norm_num : (0:ℝ)≤1/8)
  refine (Real.sqrt_le_sqrt e).trans_eq ?_
  norm_num [← Real.sqrt_mul (by norm_num : 0≤(1/8:ℝ)), ←pow_two, Real.sqrt_sq (by norm_num : 0≤(1/8:ℝ))]

theorem actual_raw_far_interval_cap {b d : ℕ} [NeZero (2^d-1)] (hd : 0<d)
    (g : (LabelField d)ˣ) (hg : orderOf g=2^d-1) {t : Fin (b+1) → LabelField d}
    (ht : LinearIndependent (ZMod 2) t) (hdim : 2*(b+1)≤d)
    (hS : MultiplicativeSidon {x : LabelField d | x ∈ labelSpace t ∧ x ≠ 0})
    (h0 : ∀ a, labelValue t a ≠ 0)
    (hp : Function.Injective (fun z : Sym2 (NonzeroBinary (b+1)) => eval t (symLabelProduct z)))
    (hadj : ∀ p q : UnequalLabels (b+1),
      labelValue t p.1.1 * labelValue t q.1.2 ≠
        (g:LabelField d) * (labelValue t p.1.2 * labelValue t q.1.1))
    (k : ℤ) {θ : ℝ} (hθ : θ∈Icc (0:ℝ) 1)
    (hk : (k:ZMod (2^d-1)) ≠ 0) (hks : (k:ZMod (2^d-1))+1 ≠ 0) :
    |rawCorrelation (ordinalPhaseLabel hd g hg t) ((k:ℝ)+θ)| ≤
       paperFarRawCap (b+1) (2^d-1) := by
  obtain ⟨C,hC,hCases⟩ := actual_raw_far_unique_correction hd (Nat.succ_pos b) g hg
    ht hdim hS h0 hp hadj k hθ hk hks
  have hbC : |C| ≤ paperWalshQ (b+1) := by
    rcases hCases with rfl | ⟨a,c,hac, e | e⟩
    · simp [paperWalshQ]
    · rw [e,rawWalshLeft]
      exact walshShift_distinct_le_Q a c hac (by linarith [hθ.2]) (by norm_num)
        (by linarith [hθ.1]) (by linarith [hθ.1]) (by linarith)
    · rw [e,rawWalshRight]
      simp_rw [add_sub_assoc]
      exact walshShift_distinct_le_Q a c hac (by linarith [hθ.1])
        (by linarith [hθ.2]) (by norm_num) (by linarith) (by linarith [hθ.2])
  let K : ℝ := ((2^d-1:ℕ):ℝ)
  let B : ℕ := 2^(b+1)
  let E := 1/(12*((2:ℝ)^(b+1))^2)
  let U := unitRotatedInner (midpointError B) θ
  let Z := unitRotatedInner (cellPrimitive (labelCellMidpoint (0:Fin B))) θ
  have hB : 0<B := by dsimp [B]; positivity
  have hK : 0<K := by
    dsimp [K]
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne (2^d-1))
  have hq : (2:ℝ)^d=K+1 := by
    have hh : 0<(2^d:ℕ) := by positivity
    dsimp [K]
    exact_mod_cast (Nat.sub_add_cancel (show 1≤(2^d:ℕ) by omega)).symm
  have hU : |U| ≤ E := by
    dsimp [U,E]
    refine (unitRotatedInner_abs_le_energy hθ (midpointError_measurable hB)
      (fun _ hr => midpointError_abs_le_one hB hr)).trans_eq ?_
    rw [midpointError_period_energy hB]
    dsimp [B]
    push_cast
    rfl
  have hZ : |Z| ≤ 1/3 := by
    dsimp [Z]
    exact (unitRotatedInner_abs_le_energy hθ (cellPrimitive_measurable _)
      (fun _ hr => cellPrimitive_abs_le_one hr)).trans (label_zero_energy_le_third hB)
  have hE : E ≤ 1/48 := by
    dsimp [E]
    have h2 : 2≤(2:ℝ)^(b+1) := by
      rw [pow_succ]
      have h := one_le_pow₀ (by norm_num : 1≤(2:ℝ)) (n:=b)
      linarith
    apply (div_le_iff₀ (by positivity)).mpr
    linarith [pow_le_pow_left₀ (by norm_num : 0≤(2:ℝ)) h2 2]
  change rawCorrelation _ _ = ((2:ℝ)^d/K)*(U+C)-Z/K at hC
  change |rawCorrelation _ _| ≤ paperWalshQ (b+1)+E+1/(2*K)
  rw [hC,hq,show (K+1)/K*(U+C)-Z/K=(U+C)+((U+C)-Z)/K by
    field_simp [hK.ne']; ring]
  have hT := (abs_add_le U C).trans (add_le_add hU hbC)
  have hA : |(U+C)-Z| ≤ 1/2 := by
    calc
      _ ≤ |U+C|+|Z| := by simpa only [sub_eq_add_neg,abs_neg] using abs_add_le (U+C) (-Z)
      _ ≤ 1/2 := by linarith [paperWalshQ_one_eighth b]
  have hD := div_le_div_of_nonneg_right hA hK.le
  refine (abs_add_le _ _).trans ?_
  rw [abs_div,abs_of_pos hK]
  have e : (1/2:ℝ)/K=1/(2*K) := by ring
  rw [e] at hD
  linarith

theorem actual_raw_far_cap {b d : ℕ} [NeZero (2^d-1)] (hd : 0<d)
    (g : (LabelField d)ˣ) (hg : orderOf g=2^d-1) {t : Fin (b+1) → LabelField d}
    (ht : LinearIndependent (ZMod 2) t) (hdim : 2*(b+1)≤d)
    (hS : MultiplicativeSidon {x : LabelField d | x ∈ labelSpace t ∧ x ≠ 0})
    (h0 : ∀ a, labelValue t a ≠ 0)
    (hp : Function.Injective (fun z : Sym2 (NonzeroBinary (b+1)) => eval t (symLabelProduct z)))
    (hadj : ∀ p q : UnequalLabels (b+1),
      labelValue t p.1.1 * labelValue t q.1.2 ≠
        (g:LabelField d) * (labelValue t p.1.2 * labelValue t q.1.1))
    (z : ℝ) (h₁ : ((⌊z⌋:ℤ):ZMod (2^d-1))≠0)
    (h₂ : (((⌊z⌋:ℤ)+1:ℤ):ZMod (2^d-1))≠0) :
    |rawCorrelation (ordinalPhaseLabel hd g hg t) z| ≤ paperFarRawCap (b+1) (2^d-1) := by
  let k : ℤ := ⌊z⌋
  let θ := z-(k:ℝ)
  have hθ : θ∈Icc (0:ℝ) 1 :=
    ⟨Int.fract_nonneg z, (Int.fract_lt_one z).le⟩
  have h₂' : (k:ZMod (2^d-1))+1 ≠ 0 := by simpa [k,Int.cast_add,Int.cast_one] using h₂
  have h := actual_raw_far_interval_cap hd g hg ht hdim hS h0 hp hadj k hθ h₁ h₂'
  simpa [θ] using h

#print axioms actual_raw_far_cap
end CenteredCubeSqrt
