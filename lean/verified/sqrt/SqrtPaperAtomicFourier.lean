import SqrtActualAtomFourierBound

namespace CenteredCubeSqrt
open scoped BigOperators
open Complex

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

noncomputable def actualFourierAtomSum {B K : ℕ} [NeZero K] (f : ZMod K → Fin B) (m : ℕ) : ℂ :=
  ∑ j : ZMod K, Complex.exp (2*(Real.pi:ℂ)*I*(m:ℂ)*(paperAtomCenter f j:ℂ))

theorem paper_atom_Fourier_coefficient {b d : ℕ} [NeZero (2^d-1)] (hd : 0<d)
    (g : (LabelField d)ˣ) (hg : orderOf g=2^d-1)
    (t : Fin b → LabelField d) (ht : ∀ i,t i ≠ 0) {m : ℕ} (hm0 : 0<m) (hmK : m<2^d-1) :
    let A := 1-1/(2:ℝ)^b
    let K := ((2^d-1:ℕ):ℝ)
    let f := ordinalPhaseLabel hd g hg t
    |(actualFourierAtomSum f m).re|/(Real.pi*(m:ℝ)) ≤
      A*Real.sqrt (K+1)/K+Real.pi*(m:ℝ)*A^2/(2*K) := by
  let A := 1-1/(2:ℝ)^b
  let K := ((2^d-1:ℕ):ℝ)
  let f := ordinalPhaseLabel hd g hg t
  let τ := 2*Real.pi*(m:ℝ)/K
  have hK : 0<K := by
    unfold K
    exact_mod_cast (show 0<(2^d-1:ℕ) by omega)
  have hm : 0<(m:ℝ) := by exact_mod_cast hm0
  have hτ : 0<τ := by unfold τ; positivity
  have heq : K+1=((2^d:ℕ):ℝ) := by
    unfold K
    have h : 0<(2^d:ℕ) := by positivity
    exact_mod_cast (Nat.sub_add_cancel (show 1≤2^d by omega))
  have h := atom_phase_sum_bound Finset.univ (coarsePhase m)
    (atomPhaseOffset f) (t:=τ) (A:=A) hτ.le
    (fun j _ => coarsePhase_norm m j) (fun j _ => paperAtomOffset_abs_le f j)
    (coarsePhase_cancel hm0 hmK) (actual_weighted_atom_phase_bound hd g hg t ht hm0 hmK)
  rw [Finset.card_univ,ZMod.card,←heq] at h
  have hrep : actualFourierAtomSum f m = Complex.exp (I*((τ/2:ℝ):ℂ)) *
      (∑ j : ZMod (2^d-1), coarsePhase m j * Complex.exp (I*((τ*atomPhaseOffset f j:ℝ):ℂ))) := by
    unfold actualFourierAtomSum
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    unfold atomPhaseOffset paperAtomCenter coarsePhase τ K
    rw [←Complex.exp_add,←Complex.exp_add]
    congr 1
    push_cast
    ring
  have e : ‖actualFourierAtomSum f m‖ ≤ τ*(A/2*Real.sqrt (K+1))+K*τ^2*A^2/8 := by
    rw [hrep,norm_mul,Complex.norm_exp_I_mul_ofReal,one_mul]
    exact h
  change |(actualFourierAtomSum f m).re|/(Real.pi*(m:ℝ)) ≤
    A*Real.sqrt (K+1)/K+Real.pi*(m:ℝ)*A^2/(2*K)
  refine (div_le_div_of_nonneg_right ((Complex.abs_re_le_norm _).trans e) (by positivity)).trans_eq ?_
  unfold τ
  field_simp [hK.ne',hm.ne',Real.pi_ne_zero] ; ring

#print axioms paper_atom_Fourier_coefficient

end CenteredCubeSqrt
