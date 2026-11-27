import SqrtCyclicStates
import SqrtTraceCharacter
import Mathlib.NumberTheory.GaussSum
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

namespace CenteredCubeSqrt
open AddChar
open scoped BigOperators

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
noncomputable local instance (d : ℕ) : Fintype (LabelField d) := Fintype.ofFinite _

theorem gaussSum_norm_sq_eq_card {F : Type*} [Field F] [Fintype F]
    {χ : MulChar F ℂ} (hχ : χ ≠ 1) {ψ : AddChar F ℂ} (hψ : ψ ≠ 1) :
    ‖gaussSum χ ψ‖^2 = (Fintype.card F:ℝ) := by
  have hh := gaussSum_mul_gaussSum_eq_card hχ (IsPrimitive.of_ne_one hψ)
  rw [←star_gaussSum_eq] at hh
  change gaussSum χ ψ * starRingEnd ℂ (gaussSum χ ψ) = _ at hh
  rw [Complex.mul_conj'] at hh
  exact_mod_cast hh

noncomputable def traceFieldCharacter {d : ℕ} (c : LabelField d) :
    AddChar (LabelField d) ℂ where
  toFun x := (bitCharacter (Algebra.traceForm (ZMod 2) (LabelField d) c x):ℂ)
  map_zero_eq_one' := by
    rw [map_zero]
    have h0 : (0:ZMod 2).val=0 := rfl
    simp [bitCharacter,h0]
  map_add_eq_mul' x y := by
    rw [map_add,bitCharacter_add,Complex.ofReal_mul]

theorem traceFieldCharacter_ne_one {d : ℕ} {c : LabelField d} (hc : c ≠ 0) :
    traceFieldCharacter c ≠ 1 := by
  intro hh
  have h : Algebra.traceForm (ZMod 2) (LabelField d) c = 0 := by
    ext x
    rcases zmod_two_zero_or_one (Algebra.traceForm (ZMod 2) (LabelField d) c x) with h | h
    · exact h
    · have e := congrArg (fun (f : AddChar (LabelField d) ℂ) => f x) hh
      change (bitCharacter (Algebra.traceForm (ZMod 2) (LabelField d) c x):ℂ)=1 at e
      have h1 : (1:ZMod 2).val=1 := rfl
      rw [h] at e
      norm_num [bitCharacter,h1] at e
  have e : Algebra.traceForm (ZMod 2) (LabelField d) c =
      Algebra.traceForm (ZMod 2) (LabelField d) 0 := by rwa [map_zero]
  exact hc ((actual_label_trace_injective d) e)


noncomputable def frequencyOnStates {d : ℕ} [NeZero (2^d-1)] (hd : 0<d)
    (g : (LabelField d)ˣ) (hg : orderOf g=2^d-1) (m : ℕ) (u : (LabelField d)ˣ) : ℂ :=
  ZMod.stdAddChar ((m:ZMod (2^d-1))* Multiplicative.toAdd ((cyclicStateEquiv hd g hg).symm u))

theorem frequencyOnStates_nonzero {d : ℕ} [NeZero (2^d-1)] (hd : 0<d)
    (g : (LabelField d)ˣ) (hg : orderOf g=2^d-1) (m : ℕ) (u : (LabelField d)ˣ) :
    frequencyOnStates hd g hg m u ≠ 0 := by
  unfold frequencyOnStates
  rw [ZMod.stdAddChar_apply]
  exact fun h => by simpa [h] using (Circle.norm_coe (ZMod.toCircle
    ((m:ZMod (2^d-1))* Multiplicative.toAdd ((cyclicStateEquiv hd g hg).symm u))))

noncomputable def paperMultiplicativeChar {d : ℕ} [NeZero (2^d-1)] (hd : 0<d)
    (g : (LabelField d)ˣ) (hg : orderOf g=2^d-1) (m : ℕ) : MulChar (LabelField d) ℂ :=
  MulChar.ofUnitHom {
    toFun := fun u => Units.mk0 (frequencyOnStates hd g hg m u) (frequencyOnStates_nonzero hd g hg m u)
    map_one' := by
      ext
      change frequencyOnStates hd g hg m 1 = 1
      simp [frequencyOnStates]
    map_mul' := by
      intro x y
      ext
      change frequencyOnStates hd g hg m (x*y) =
        frequencyOnStates hd g hg m x * frequencyOnStates hd g hg m y
      unfold frequencyOnStates
      rw [(cyclicStateEquiv hd g hg).symm.map_mul]
      change ZMod.stdAddChar ((m:ZMod (2^d-1))*(Multiplicative.toAdd ((cyclicStateEquiv hd g hg).symm x) +
        Multiplicative.toAdd ((cyclicStateEquiv hd g hg).symm y))) = _
      rw [mul_add,map_add_eq_mul] }

theorem paperMultiplicativeChar_ne_one {d : ℕ} [NeZero (2^d-1)] (hd : 0<d)
    (g : (LabelField d)ˣ) (hg : orderOf g=2^d-1) {m : ℕ}
    (hm0 : 0<m) (hmK : m<2^d-1) : paperMultiplicativeChar hd g hg m ≠ 1 := by
  intro hh
  let u : (LabelField d)ˣ := cyclicStateEquiv hd g hg (Multiplicative.ofAdd 1)
  have e := congrArg (fun (f : MulChar (LabelField d) ℂ) => f u) hh
  change paperMultiplicativeChar hd g hg m u = (1:MulChar (LabelField d) ℂ) u at e
  rw [MulChar.one_apply u.isUnit] at e
  have E : ZMod.stdAddChar (m:ZMod (2^d-1)) = 1 := by
    rw [paperMultiplicativeChar,MulChar.ofUnitHom_coe] at e
    change frequencyOnStates hd g hg m u = 1 at e
    rw [frequencyOnStates] at e
    dsimp only [u] at e
    rw [MulEquiv.symm_apply_apply] at e
    change ZMod.stdAddChar ((m:ZMod (2^d-1))*1) = 1 at e
    rwa [mul_one] at e
  have F : (m:ZMod (2^d-1))=0 :=
    ZMod.injective_stdAddChar (E.trans (map_zero_eq_one ZMod.stdAddChar).symm)
  have v := congrArg ZMod.val F
  rw [ZMod.val_natCast_of_lt hmK,ZMod.val_zero] at v
  omega

theorem actual_paperGauss_norm_sq {d : ℕ} [NeZero (2^d-1)] (hd : 0<d)
    (g : (LabelField d)ˣ) (hg : orderOf g=2^d-1) {m : ℕ}
    (hm0 : 0<m) (hmK : m<2^d-1) {c : LabelField d} (hc : c ≠ 0) :
    ‖gaussSum (paperMultiplicativeChar hd g hg m) (traceFieldCharacter c)‖^2 = ((2^d:ℕ):ℝ) := by
  have e := gaussSum_norm_sq_eq_card (paperMultiplicativeChar_ne_one hd g hg hm0 hmK)
    (traceFieldCharacter_ne_one hc)
  simpa [←Nat.card_eq_fintype_card,labelField_card hd] using e

#print axioms actual_paperGauss_norm_sq

end CenteredCubeSqrt
