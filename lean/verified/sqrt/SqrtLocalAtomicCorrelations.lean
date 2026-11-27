import SqrtActualLocalWeights

namespace CenteredCubeSqrt

open MeasureTheory
open scoped BigOperators Interval
open Classical

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem atom_pulse_correlation_normalized {B K : ℕ} [NeZero K] [NeZero (B*K)]
    (f : ZMod K → Fin B) {eps s t s' t' v M a b : ℝ}
    (he : 0 < eps) (hv : 0 < v) (hm : M/((K:ℝ)*v) < 1/4)
    (hs : -M ≤ s-eps/2) (ht : t+eps/2 ≤ M)
    (hs' : -M ≤ s'-eps/2) (ht' : t'+eps/2 ≤ M) :
    v*(∫ x in (0:ℝ)..1,
      atomPulseTrain f eps s t ((K:ℝ)*v) a x * atomPulseTrain f eps s' t' ((K:ℝ)*v) b x) =
      ∑ r : ZMod (B*K), atomWeight f (b-a) r *
        pulseOverlap eps s t s' t' (((K:ℝ)*v)*((atomResidueLift (b-a) r : ℝ)/((B:ℝ)*K)+(b-a))) := by
  have hK : 0 < (K:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne K)
  rw [atomPulseTrain_correlation f he (mul_pos hK hv) hm hs ht hs' ht', ← mul_assoc]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  unfold atomWeight
  field_simp

/-- Extract precisely the coincident-atom contribution of a same-side
correlation. This is exact; the remaining weight is supported on r≠0. -/
theorem same_atom_correlation_diagonal {B K : ℕ} [NeZero K] [NeZero (B*K)]
    (hB : 0 < B) (f : ZMod K → Fin B) (kernel : ZMod (B*K) → ℝ) :
    (∑ r : ZMod (B*K), atomWeight f 0 r * kernel r) =
      kernel 0 + ∑ r : ZMod (B*K), (if r=0 then 0 else atomWeight f 0 r)*kernel r := by
  have e (r : ZMod (B*K)) : atomWeight f 0 r*kernel r =
      (if r=0 then kernel 0 else 0)+(if r=0 then 0 else atomWeight f 0 r)*kernel r := by
    by_cases h : r=0
    · simp [h,atomWeight_zero hB f]
    · simp [h]
  simp_rw [e,Finset.sum_add_distrib]
  simp

/-- Same-side pulse-pair contribution: exact leading term and explicit
uniform error of order B^−2 after the natural v rescaling. -/
theorem actual_same_side_correlation_budget {b d : ℕ} [NeZero (2^d-1)]
    [NeZero (2^b*(2^d-1))] (hd : 0 < d) (g : (LabelField d)ˣ)
    (hg : orderOf g = 2^d-1) {tβ : Fin b → LabelField d}
    (htβ : LinearIndependent (ZMod 2) tβ) (hdim : 2*b ≤ d)
    (h1 : (phaseState hd g hg 1 : LabelField d) ≠ 1)
    (h1' : (phaseState hd g hg 1 : LabelField d) ∉ labelRatioSet tβ)
    {v eps T s t s' t' a : ℝ} {D : ℕ}
    (hv : 0 < v) (he : 0 < eps) (hT : 0 ≤ T)
    (hV : 2*T+eps < v) (hBv : ((2^b:ℕ):ℝ) ≤ 2*v)
    (hD : 2*(2*T+eps)+1 ≤ D)
    (hm : (T+eps/2)/((((2^d-1:ℕ):ℝ))*v) < 1/4)
    (hs : -T ≤ s) (hst : s ≤ t) (ht : t ≤ T) (hs' : -T ≤ s') (ht' : t' ≤ T) :
    let f := ordinalPhaseLabel hd g hg tβ
    let C := (((2^d-1:ℕ):ℝ))*v
    let Cov := v*(∫ x in (0:ℝ)..1, atomPulseTrain f eps s t C a x *
      atomPulseTrain f eps s' t' C a x)
    0 ≤ Cov - pulseOverlap eps s t s' t' 0 ∧
    Cov - pulseOverlap eps s t s' t' 0 ≤
      (2*(D:ℝ)+1)*(4*(2*T+eps)/(((2^b:ℕ):ℝ)^2))*(2*T) := by
  let f := ordinalPhaseLabel hd g hg tβ
  let K : ℕ := 2^d-1
  let B : ℕ := 2^b
  have hK : 0<K := Nat.pos_of_ne_zero (NeZero.ne K)
  have hB : 0<B := by dsimp [B]; positivity
  let w := fun r : ZMod (B*K) => if r=0 then 0 else atomWeight f 0 r
  have hw : ∀ r ∈ physicalWindowResidues (B:=B) (K:=K) v (2*T+eps) 0,
      0 ≤ w r ∧ w r ≤ 4*(2*T+eps)/(B:ℝ)^2 := by
    intro r hr
    by_cases h : r=0
    · unfold w
      rw [ite_eq_left h]
      exact ⟨le_rfl,by positivity⟩
    · unfold w
      rw [ite_eq_right h]
      exact actual_atom_weight_small hd g hg htβ hdim h1 h1' hv
        ⟨by linarith, hV⟩ hBv h hr
  have hErr := physical_overlap_sum_budget hB hK hv he hT hBv hD hs hst ht hs' ht'
    w (by positivity : 0 ≤ 4*(2*T+eps)/(B:ℝ)^2) hw
  dsimp
  rw [atom_pulse_correlation_normalized f he hv hm
    (show -(T+eps/2) ≤ s-eps/2 by linarith)
    (show t+eps/2 ≤ T+eps/2 by linarith)
    (show -(T+eps/2) ≤ s'-eps/2 by linarith)
    (show t'+eps/2 ≤ T+eps/2 by linarith),
    sub_self, same_atom_correlation_diagonal hB]
  simp only [atomResidueLift_zero_zero, Int.cast_zero,zero_div,zero_add,mul_zero,
    add_sub_cancel_left]
  exact hErr

/-- Opposite-side integral: every contributing bin is a safe mirror bin,
with actual weight bounded by 2/B. -/
theorem actual_mirror_correlation_budget {b d : ℕ} [NeZero (2^d-1)]
    [NeZero (2^b*(2^d-1))] (hd : 0 < d) (g : (LabelField d)ˣ)
    (hg : orderOf g = 2^d-1) {tβ : Fin b → LabelField d}
    (htβ : LinearIndependent (ZMod 2) tβ) (hdim : 2*b ≤ d)
    {v eps T L0 s t s' t' a b0 : ℝ} {D : ℕ}
    (hoff : b0-a=-L0)
    (hv : 0 < v) (he : 0 < eps) (hT : 0 ≤ T)
    (hV : 2*T+eps < v) (hBv : ((2^b:ℕ):ℝ) ≤ 2*v)
    (hD : 2*(2*T+eps)+1 ≤ D)
    (hm : (T+eps/2)/((((2^d-1:ℕ):ℝ))*v) < 1/4)
    (hs : -T ≤ s) (hst : s ≤ t) (ht : t ≤ T) (hs' : -T ≤ s') (ht' : t' ≤ T)
    (hSafe : ∀ k : ℤ, |(k:ℝ)-(((2^d-1:ℕ):ℝ))*L0| < 2 →
      (phaseState hd g hg (k:ZMod (2^d-1)) : LabelField d) ≠ 1 ∧
      (phaseState hd g hg (k:ZMod (2^d-1)) : LabelField d) ∉ labelRatioSet tβ) :
    let f := ordinalPhaseLabel hd g hg tβ
    let C := (((2^d-1:ℕ):ℝ))*v
    let Cov := v*(∫ x in (0:ℝ)..1, atomPulseTrain f eps s t C a x *
      atomPulseTrain f eps s' t' C b0 x)
    0 ≤ Cov ∧ Cov ≤ (2*(D:ℝ)+1)*(2/((2^b:ℕ):ℝ))*(2*T) := by
  let f := ordinalPhaseLabel hd g hg tβ
  let K : ℕ := 2^d-1
  let B : ℕ := 2^b
  have hK : 0<K := Nat.pos_of_ne_zero (NeZero.ne K)
  have hB : 0<B := by dsimp [B]; positivity
  have hErr := physical_overlap_sum_budget hB hK hv he hT hBv hD hs hst ht hs' ht'
    (atomWeight f (-L0)) (by positivity : 0 ≤ 2/(B:ℝ))
    (fun r hr => actual_atom_weight_mirror hd g hg htβ hdim hv ⟨by linarith,hV⟩ hSafe hr)
  dsimp
  rw [atom_pulse_correlation_normalized f he hv hm
    (show -(T+eps/2) ≤ s-eps/2 by linarith)
    (show t+eps/2 ≤ T+eps/2 by linarith)
    (show -(T+eps/2) ≤ s'-eps/2 by linarith)
    (show t'+eps/2 ≤ T+eps/2 by linarith),
    hoff]
  exact hErr

#print axioms actual_same_side_correlation_budget
#print axioms actual_mirror_correlation_budget

end CenteredCubeSqrt
