import SqrtPlateauFourierExact
import Mathlib.Topology.Algebra.InfiniteSum.Real

namespace CenteredCubeSqrt
open Set
open scoped BigOperators

theorem inverseFourth_step {y : ℝ} (hy : 0<y) :
    1/(y+1)^4 ≤ (1/y^3-1/(y+1)^3)/3 := by
  have hp : 0 < y+1 := by positivity
  apply le_of_mul_le_mul_left _ (show 0<3*y^3*(y+1)^4 by positivity)
  have e1 : (3*y^3*(y+1)^4)*(1/(y+1)^4)=3*y^3 := by field_simp
  have e2 : (3*y^3*(y+1)^4)*((1/y^3-1/(y+1)^3)/3) =
      (y+1)^4-y^3*(y+1) := by field_simp
  rw [e1,e2]
  have e : (y+1)^4-y^3*(y+1)-3*y^3=6*y^2+4*y+1 := by ring
  linarith [show 0≤6*y^2+4*y+1 by positivity]

theorem inverseFourth_tail (M : ℕ) (hM : 0<M) :
    (∑' j : ℕ, 1/((M:ℝ)+(j:ℝ)+1)^4) ≤ 1/(3*(M:ℝ)^3) := by
  have hmr : 0<(M:ℝ) := by exact_mod_cast hM
  apply Real.tsum_le_of_sum_range_le (fun j => by positivity)
  intro n
  have H (k : ℕ) :
      (∑ j ∈ Finset.range k, 1/((M:ℝ)+(j:ℝ)+1)^4) ≤
        ((1/(M:ℝ)^3) - (1/((M:ℝ)+(k:ℝ))^3))/3 := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ,Nat.cast_succ]
      have hk := inverseFourth_step (y:=(M:ℝ)+(k:ℝ)) (by positivity)
      rw [←add_assoc]
      linarith
  have hk := H n
  have he : (1/(M:ℝ)^3)/3 = 1/(3*(M:ℝ)^3) := by ring
  rw [←he]
  linarith [show 0≤1/((M:ℝ)+(n:ℝ))^3 by positivity]

noncomputable def plateauSumTerm (L : ℝ) (m : ℕ) : ℝ :=
  plateauSpectralCoeff m*(Real.sin (Real.pi*(m:ℝ)*L))^2

noncomputable def finitePlateau (M : ℕ) (L : ℝ) : ℝ :=
  1+∑ j ∈ Finset.range M, plateauSumTerm L (j+1)

theorem plateauSumTerm_nonnegative (L : ℝ) (m : ℕ) : 0≤plateauSumTerm L m :=
  mul_nonneg (plateauSpectralCoeff_nonneg _) (sq_nonneg _)

theorem plateauSumTerm_majorant (L : ℝ) {m : ℕ} (hm : 0<m) :
    plateauSumTerm L m ≤ (144/29)/((m:ℝ)^4) := by
  have m0 : 0<(m:ℝ) := by exact_mod_cast hm
  have hs : (Real.sin (Real.pi*(m:ℝ)*L))^2≤1 := by
    rw [←sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (Real.abs_sin_le_one _) 2 |>.trans_eq (by norm_num)
  have hπ : (81:ℝ) ≤ Real.pi^4 := by
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤3) Real.pi_gt_three.le 4
    norm_num at h
    exact h
  dsimp [plateauSumTerm]
  calc
    _ ≤ plateauSpectralCoeff m := mul_le_of_le_one_right (plateauSpectralCoeff_nonneg _) hs
    _ ≤ _ := (plateauCoeff_majorant _ m0).trans (by
      calc
        _ ≤ 16*(729/29)/(81*(m:ℝ)^4) :=
          div_le_div_of_nonneg_left (by norm_num) (by positivity)
            (mul_le_mul_of_nonneg_right hπ (by positivity))
        _ = _ := by ring)

theorem paper_plateau_finite_tail {L : ℝ} (hL : L∈Icc (10/9:ℝ) (11/9))
    {M : ℕ} (hM : 0<M) :
    0≤(27/29)*L^2-finitePlateau M L ∧
      (27/29)*L^2-finitePlateau M L ≤ 48/(29*(M:ℝ)^3) := by
  let g := plateauSumTerm L
  let f (j : ℕ) := g (j+1)
  have Hg : HasSum g ((27/29)*L^2-1) := paper_plateau_series_exact hL
  have hz : g 0=0 := by simp [g,plateauSumTerm]
  have hf : Summable f := (summable_nat_add_iff 1).2 Hg.summable
  have heq := Hg.summable.tsum_eq_zero_add
  rw [Hg.tsum_eq,hz,zero_add] at heq
  have hpart := hf.sum_add_tsum_nat_add M
  change (∑ j ∈ Finset.range M, f j)+(∑' j : ℕ, f (j+M)) = (∑' j : ℕ, f j) at hpart
  have e : (27/29)*L^2-finitePlateau M L = ∑' j : ℕ, f (j+M) := by
    unfold finitePlateau
    change (27/29)*L^2-(1+∑ j ∈ Finset.range M, f j) = _
    linarith
  rw [e]
  refine ⟨tsum_nonneg (fun j => plateauSumTerm_nonnegative L _),?_⟩
  have hcomp (j : ℕ) : f (j+M)≤(144/29)*(1/((M:ℝ)+(j:ℝ)+1)^4) := by
    have h := plateauSumTerm_majorant L (m:=j+M+1) (by omega)
    simpa only [Nat.cast_add,Nat.cast_one,add_comm (j:ℝ) (M:ℝ),div_eq_mul_inv,one_mul] using h
  have hh := inverseFourth_tail M hM
  have hnn (j : ℕ) : 0≤(1:ℝ)/((M:ℝ)+(j:ℝ)+1)^4 := by positivity
  have hsm : Summable (fun j : ℕ => 1/((M:ℝ)+(j:ℝ)+1)^4) := by
    have h0 := (Real.summable_nat_pow_inv (p:=4)).2 (by decide)
    have h1 := (summable_nat_add_iff (M+1)).2 h0
    convert h1 using 1
    funext j
    push_cast
    rw [show (M:ℝ)+(j:ℝ)+1=(j:ℝ)+((M:ℝ)+1) by ring, one_div]
  calc
    _ ≤ ∑' j : ℕ, (144/29)*(1/((M:ℝ)+(j:ℝ)+1)^4) :=
      Summable.tsum_le_tsum hcomp ((summable_nat_add_iff M).2 hf) (hsm.mul_left _)
    _ = (144/29)*(∑' j : ℕ, 1/((M:ℝ)+(j:ℝ)+1)^4) := tsum_mul_left
    _ ≤ _ := (mul_le_mul_of_nonneg_left hh (by norm_num)).trans_eq (by ring)

#print axioms inverseFourth_tail
#print axioms paper_plateau_finite_tail

end CenteredCubeSqrt
