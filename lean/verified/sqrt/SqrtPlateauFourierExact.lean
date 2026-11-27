import SqrtPlateauFourier

namespace CenteredCubeSqrt

open Set
set_option maxHeartbeats 2500000

noncomputable def filteredQuartic (q : ℝ → ℝ) (b x : ℝ) : ℝ :=
  3*q 0-4*q b+q (2*b)-3*q x+
    2*(q (b+x)+q |b-x|)-(q (2*b+x)+q (2*b-x))/2

noncomputable def sineFourthTerm (m : ℕ) (b x : ℝ) : ℝ :=
  (Real.sin (Real.pi*(m:ℝ)*b)/(Real.pi*(m:ℝ)))^4*
    (Real.sin (Real.pi*(m:ℝ)*x))^2

theorem filteredQuartic_hasSum {b x : ℝ}
    (hb : b ∈ Icc (0:ℝ) 1) (h2b : 2*b ∈ Icc (0:ℝ) 1)
    (hx : x ∈ Icc (0:ℝ) 1) (hbx : b+x ∈ Icc (0:ℝ) 1)
    (hbmx : |b-x| ∈ Icc (0:ℝ) 1) (h2bx : 2*b+x ∈ Icc (0:ℝ) 1)
    (h2bmx : 2*b-x ∈ Icc (0:ℝ) 1) :
    HasSum (fun m : ℕ => sineFourthTerm m b x)
      (-(1/48)*filteredQuartic quarticB b x) := by
  have h0 := cosineFourth_hasSum (show (0:ℝ)∈Icc 0 1 by norm_num)
  have H := (((((h0.mul_left (3:ℝ)).sub ((cosineFourth_hasSum hb).mul_left (4:ℝ))).add
     (cosineFourth_hasSum h2b)).sub ((cosineFourth_hasSum hx).mul_left (3:ℝ))).add
     (((cosineFourth_hasSum hbx).add (cosineFourth_hasSum hbmx)).mul_left (2:ℝ))).sub
     (((cosineFourth_hasSum h2bx).add (cosineFourth_hasSum h2bmx)).div_const 2)
  have Hs := H.mul_left (1/(16*Real.pi^4))
  convert Hs using 1
  · funext m
    by_cases hm : m=0
    · subst m
      norm_num [cosineFourth,sineFourthTerm]
    · have hm' : (m:ℝ) ≠ 0 := by exact_mod_cast hm
      simp only [cosineFourth,sineFourthTerm]
      have e := sine_four_square_expand (Real.pi*(m:ℝ)*b) (Real.pi*(m:ℝ)*x)
      rw [show 2*(Real.pi*(m:ℝ)*b) = 2*Real.pi*(m:ℝ)*b by ring,
        show 2*(Real.pi*(m:ℝ)*x) = 2*Real.pi*(m:ℝ)*x by ring] at e
      have habs : Real.cos (2*Real.pi*(m:ℝ)*|b-x|) =
          Real.cos (2*Real.pi*(m:ℝ)*(b-x)) := by
        rcases le_total 0 (b-x) with h | h
        · rw [abs_of_nonneg h]
        · rw [abs_of_nonpos h,mul_neg,Real.cos_neg]
      rw [habs]
      rw [show 2*Real.pi*(m:ℝ)*(2*b)=2*(2*Real.pi*(m:ℝ)*b) by ring,
        show 2*Real.pi*(m:ℝ)*(b+x)=2*Real.pi*(m:ℝ)*b+2*Real.pi*(m:ℝ)*x by ring,
        show 2*Real.pi*(m:ℝ)*(b-x)=2*Real.pi*(m:ℝ)*b-2*Real.pi*(m:ℝ)*x by ring,
        show 2*Real.pi*(m:ℝ)*(2*b+x)=2*(2*Real.pi*(m:ℝ)*b)+2*Real.pi*(m:ℝ)*x by ring,
        show 2*Real.pi*(m:ℝ)*(2*b-x)=2*(2*Real.pi*(m:ℝ)*b)-2*Real.pi*(m:ℝ)*x by ring]
      simp only [mul_zero,Real.cos_zero,mul_one]
      generalize Real.cos (2*Real.pi*(m:ℝ)*b) = c1 at e ⊢
      generalize Real.cos (2*(2*Real.pi*(m:ℝ)*b)) = c2 at e ⊢
      generalize Real.cos (2*Real.pi*(m:ℝ)*x) = c3 at e ⊢
      generalize Real.cos (2*Real.pi*(m:ℝ)*b+2*Real.pi*(m:ℝ)*x) = c4 at e ⊢
      generalize Real.cos (2*Real.pi*(m:ℝ)*b-2*Real.pi*(m:ℝ)*x) = c5 at e ⊢
      generalize Real.cos (2*(2*Real.pi*(m:ℝ)*b)+2*Real.pi*(m:ℝ)*x) = c6 at e ⊢
      generalize Real.cos (2*(2*Real.pi*(m:ℝ)*b)-2*Real.pi*(m:ℝ)*x) = c7 at e ⊢
      field_simp [Real.pi_ne_zero,hm']
      linarith only [e]
  · unfold filteredQuartic
    field_simp [Real.pi_ne_zero]
    ring

theorem paper_plateau_series_exact {L : ℝ} (hL : L∈Icc (10/9:ℝ) (11/9)) :
    HasSum (fun m : ℕ => plateauSpectralCoeff m*(Real.sin (Real.pi*(m:ℝ)*L))^2)
      ((27/29)*L^2-1) := by
  let x := L-1
  have hx : x ∈ Icc (1/9:ℝ) (2/9) := by exact ⟨by dsimp [x]; linarith [hL.1],by dsimp [x]; linarith [hL.2]⟩
  have hx0 : x ∈ Icc (0:ℝ) 1 := ⟨by linarith [hx.1],by linarith [hx.2]⟩
  have ha : 0≤(10:ℝ)/27-x := by linarith [hx.2]
  have hs : (1:ℝ)/9-x≤0 := by linarith [hx.1]
  have ha0 := filteredQuartic_hasSum (b:=10/27) (x:=x) (by norm_num) (by norm_num) hx0
    ⟨by linarith [hx.1],by linarith [hx.2]⟩
    (by rw [abs_of_nonneg ha]; exact ⟨ha,by linarith [hx.1]⟩)
    ⟨by linarith [hx.1],by linarith [hx.2]⟩
    ⟨by linarith [hx.2],by linarith [hx.1]⟩
  have hs0 := filteredQuartic_hasSum (b:=1/9) (x:=x) (by norm_num) (by norm_num) hx0
    ⟨by linarith [hx.1],by linarith [hx.2]⟩
    (by rw [abs_of_nonpos hs]; exact ⟨by linarith [hx.1],by linarith [hx.2]⟩)
    ⟨by linarith [hx.1],by linarith [hx.2]⟩
    ⟨by linarith [hx.2],by linarith [hx.1]⟩
  have H := (ha0.add (hs0.mul_left (3:ℝ))).mul_left (4*(729/29):ℝ)
  convert H using 1
  · funext n
    have e : Real.pi*(n:ℝ)*L = Real.pi*(n:ℝ)*x+(n:ℝ)*Real.pi := by dsimp [x]; ring
    rw [e,Real.sin_add_nat_mul_pi,mul_pow,←pow_mul, mul_comm n 2, pow_mul,neg_one_sq,one_pow,one_mul]
    unfold plateauSpectralCoeff sineFourthTerm
    ring
  · unfold filteredQuartic
    rw [abs_of_nonneg ha,abs_of_nonpos hs]
    unfold quarticB x
    ring

#print axioms paper_plateau_series_exact

end CenteredCubeSqrt
