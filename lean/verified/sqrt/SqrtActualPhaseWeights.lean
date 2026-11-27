import SqrtAtomFourierRemainder
import SqrtPaperGaussActualSum
import SqrtOrdinalCyclicLabels

namespace CenteredCubeSqrt
open scoped BigOperators
open Complex

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
noncomputable local instance (d : ℕ) : Fintype (LabelField d) := Fintype.ofFinite _

noncomputable def atomPhaseOffset {B K : ℕ} [NeZero K] (f : ZMod K → Fin B)
    (j : ZMod K) : ℝ := (((f j).val:ℝ)+1/2)/(B:ℝ)-1/2

noncomputable def phaseBitWeight {b : ℕ} (i : Fin b) : ℝ := 2^(i.val:ℕ)/(2*(2:ℝ)^b)

theorem sum_two_powers (b : ℕ) : ∑ i : Fin b,(2:ℝ)^i.val = (2:ℝ)^b-1 := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [Fin.sum_univ_castSucc]
    change (∑ i : Fin b,(2:ℝ)^i.val)+(2:ℝ)^b=(2:ℝ)^(b+1)-1
    rw [ih,pow_succ]
    ring

theorem real_bit_eq_one_sub_character (z : ZMod 2) :
    (z.val:ℝ) = (1-bitCharacter z)/2 := by
  have h0 : (0:ZMod 2).val=0 := rfl
  have h1 : (1:ZMod 2).val=1 := rfl
  rcases zmod_two_zero_or_one z with rfl|rfl <;> norm_num [bitCharacter,h0,h1]

theorem exact_phaseOffset_character_expansion {b d : ℕ} [NeZero (2^d-1)] (hd : 0<d) (g : (LabelField d)ˣ)
    (hg : orderOf g=2^d-1) (t : Fin b → LabelField d) (j : ZMod (2^d-1)) :
    (atomPhaseOffset (ordinalPhaseLabel hd g hg t) j:ℂ) =
      -(∑ i : Fin b,(phaseBitWeight i:ℂ)*
        traceFieldCharacter (t i) (phaseState hd g hg j : LabelField d)) := by
  have c : (∑ i : Fin b, (2:ℝ) ^ i.val * ((phaseLabel hd g hg t j i).val:ℝ)) =
      ((ordinalPhaseLabel hd g hg t j).val:ℝ) := by
    unfold ordinalPhaseLabel
    rw [binaryLabelEquiv_val]
    push_cast
    rfl
  unfold atomPhaseOffset
  rw [←c]
  have e : (∑ i : Fin b, (2:ℝ) ^ i.val * ((phaseLabel hd g hg t j i).val:ℝ)) =
    ((2:ℝ)^b-1)/2-∑ i : Fin b, (2:ℝ)^i.val/2 * bitCharacter (phaseLabel hd g hg t j i) := by
    simp_rw [real_bit_eq_one_sub_character]
    simp_rw [show ∀ a c : ℝ, a*((1-c)/2)=a/2-a/2*c by intros; ring]
    rw [Finset.sum_sub_distrib,←Finset.sum_div,sum_two_powers]
  rw [e]
  push_cast
  have hsum : (∑ i : Fin b, (2:ℂ)^i.val/2 *
    (bitCharacter (phaseLabel hd g hg t j i):ℂ))/((2:ℂ)^b) =
     ∑ i : Fin b,(phaseBitWeight i:ℂ)*traceFieldCharacter (t i) (phaseState hd g hg j : LabelField d) := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    unfold phaseBitWeight traceFieldCharacter phaseLabel
    change (2:ℂ)^i.val/2*(bitCharacter (traceLabelMap t (phaseState hd g hg j : LabelField d) i):ℂ)/
      (2:ℂ)^b = ((2^(i.val:ℕ)/(2*(2:ℝ)^b):ℝ):ℂ)*
        (bitCharacter (Algebra.traceForm (ZMod 2) (LabelField d) (t i) (phaseState hd g hg j : LabelField d)):ℂ)
    simp only [traceLabelMap_apply,Algebra.traceForm_apply]
    push_cast
    ring
  rw [←hsum]
  have hn : ((2:ℂ)^b) ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp [hn]
  ring

theorem phaseBitWeight_sum (b : ℕ) :
    (∑ i : Fin b, phaseBitWeight i) = (1-1/(2:ℝ)^b)/2 := by
  unfold phaseBitWeight
  rw [←Finset.sum_div,sum_two_powers]
  field_simp

theorem paperAtomOffset_abs_le {b K : ℕ} [NeZero K] (f : ZMod K → Fin (2^b)) (j : ZMod K) :
    |atomPhaseOffset f j| ≤ (1-1/(2:ℝ)^b)/2 := by
  unfold atomPhaseOffset
  push_cast
  have hp : 0 < (2:ℝ)^b := by positivity
  have hj : ((f j).val:ℝ)+1 ≤ (2:ℝ)^b := by
    exact_mod_cast (Nat.succ_le_of_lt (f j).isLt)
  apply abs_le.mpr
  constructor <;> apply (le_of_mul_le_mul_left _ hp) <;>
    field_simp <;> linarith [Nat.cast_nonneg (α:=ℝ) (f j).val]

#print axioms exact_phaseOffset_character_expansion
#print axioms phaseBitWeight_sum
#print axioms paperAtomOffset_abs_le

end CenteredCubeSqrt
