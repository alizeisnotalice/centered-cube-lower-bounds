import SqrtPaperGaussNorm

namespace CenteredCubeSqrt

open scoped BigOperators
open Complex

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
noncomputable local instance (d : ℕ) : Fintype (LabelField d) := Fintype.ofFinite _

theorem paperGauss_as_cyclic_sum {d : ℕ} [NeZero (2^d-1)] (hd : 0<d)
    (g : (LabelField d)ˣ) (hg : orderOf g=2^d-1) (m : ℕ) (c : LabelField d) :
    gaussSum (paperMultiplicativeChar hd g hg m) (traceFieldCharacter c) =
      ∑ j : ZMod (2^d-1), ZMod.stdAddChar ((m:ZMod (2^d-1))*j) *
        traceFieldCharacter c (↑(cyclicStateEquiv hd g hg (Multiplicative.ofAdd j))) := by
  classical
  unfold gaussSum
  rw [Fintype.sum_eq_add_sum_subtype_ne _ (0 : LabelField d),MulChar.map_zero,zero_mul,zero_add]
  let e : ZMod (2^d-1) ≃ {x : LabelField d // x≠0} :=
    Multiplicative.ofAdd.trans ((cyclicStateEquiv hd g hg).toEquiv.trans unitsEquivNeZero)
  symm
  refine Fintype.sum_equiv e _ _ (fun j => ?_)
  let u := cyclicStateEquiv hd g hg (Multiplicative.ofAdd j)
  change ZMod.stdAddChar ((m:ZMod (2^d-1))*j)*traceFieldCharacter c ↑u =
    paperMultiplicativeChar hd g hg m ↑u*traceFieldCharacter c ↑u
  congr 1
  rw [paperMultiplicativeChar,MulChar.ofUnitHom_coe]
  change _ = frequencyOnStates hd g hg m u
  simp only [frequencyOnStates,u,MulEquiv.symm_apply_apply]
  rfl

theorem paperGauss_as_exp_trace_sum {d : ℕ} [NeZero (2^d-1)] (hd : 0<d)
    (g : (LabelField d)ˣ) (hg : orderOf g=2^d-1) (m : ℕ) (c : LabelField d) :
    gaussSum (paperMultiplicativeChar hd g hg m) (traceFieldCharacter c) =
      ∑ j : ZMod (2^d-1), Complex.exp
        (2*(Real.pi:ℂ)*I*(m:ℂ)*(j.val:ℂ)/((2^d-1:ℕ):ℂ)) *
        traceFieldCharacter c (↑(cyclicStateEquiv hd g hg (Multiplicative.ofAdd j))) := by
  rw [paperGauss_as_cyclic_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  congr 1
  have hcast : ((((m*j.val:ℕ):ℤ)):ZMod (2^d-1)) = (m:ZMod (2^d-1))*j := by
    push_cast
    rw [ZMod.natCast_zmod_val]
  rw [←hcast,ZMod.stdAddChar_coe]
  push_cast
  congr 1
  ring

#print axioms paperGauss_as_exp_trace_sum

end CenteredCubeSqrt
