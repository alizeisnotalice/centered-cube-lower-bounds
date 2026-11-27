import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

namespace CenteredCubeSqrt
open Filter Set
open scoped Topology
set_option maxHeartbeats 1000000

def paperPeriod (d : ℕ) : ℕ := 2^d-1

theorem paperPeriod_succ (d : ℕ) : paperPeriod (d+1)=2*paperPeriod d+1 := by
  unfold paperPeriod
  have h : 0<(2:ℕ)^d := by positivity
  rw [pow_succ]
  omega

theorem paperPeriod_one_le {d : ℕ} (hd : 0<d) : 1≤paperPeriod d := by
  have h := Nat.pow_le_pow_right (show (0:ℕ)<2 by decide) (show 1≤d by omega)
  unfold paperPeriod
  omega

theorem paperPeriod_strictMono : StrictMono paperPeriod := by
  apply strictMono_nat_of_lt_succ
  intro d
  rw [paperPeriod_succ]
  omega

theorem paper_period_max {X : ℝ} (hX : 1≤X) :
    ∃ d : ℕ, 0<d ∧ (paperPeriod d:ℝ)≤X ∧ X<(paperPeriod (d+1):ℝ) ∧
      ∀ d' : ℕ, (paperPeriod d':ℝ)≤X → d'≤d := by
  obtain ⟨N,hN⟩ := exists_nat_gt X
  have hle (j : ℕ) : j≤paperPeriod j := by
    induction j with
    | zero => simp [paperPeriod]
    | succ j ih => rw [paperPeriod_succ]; omega
  have E : ∃ j : ℕ, X<(paperPeriod j:ℝ) := by
    exact ⟨N,hN.trans_le (by exact_mod_cast hle N)⟩
  let j := Nat.find E
  have hJ : X<(paperPeriod j:ℝ) := Nat.find_spec E
  have p0 : paperPeriod 0=0 := rfl
  have p1 : paperPeriod 1=1 := rfl
  have hj : 2≤j := by
    by_contra! h
    interval_cases j <;> simp_all [paperPeriod] <;> linarith
  let d := j-1
  have hD : d+1=j := by dsimp [d]; omega
  have hd : 0<d := by dsimp [d]; omega
  have hdj : d<j := by omega
  have hi : (paperPeriod d:ℝ)≤X := le_of_not_gt (Nat.find_min E hdj)
  refine ⟨d,hd,hi,by rwa [hD],?_⟩
  intro i hi'
  by_contra! h
  have a : j ≤ i := by omega
  have b := paperPeriod_strictMono.monotone a
  exact (not_lt_of_ge hi') (hJ.trans_le (by exact_mod_cast b))

noncomputable def paperV (p : ℝ) (n d : ℕ) : ℝ := 9*p^2*(n:ℝ)/(29*(paperPeriod d:ℝ)^2)

theorem paper_v_period_prescription {p : ℝ} (hp : 0<p) {n : ℕ} (hn : 1 < n)
    (hseed : 16*Real.log n≤9*p^2*(n:ℝ)/29) :
    ∃ d : ℕ, 0<d ∧ 16*Real.log n≤paperV p n d ∧
      paperV p n d<144*Real.log n ∧ paperV p n (d+1)<16*Real.log n ∧
      ∀ e : ℕ, 0<e → 16*Real.log n≤paperV p n e → e≤d := by
  let N := 9*p^2*(n:ℝ)/29
  let logN := 16*Real.log n
  let X := Real.sqrt (N/logN)
  have hlog : 0<logN := mul_pos (by norm_num) (Real.log_pos (by exact_mod_cast hn))
  have hN : 0<N := hlog.trans_le hseed
  have X1 : 1≤X := Real.le_sqrt_of_sq_le (by norm_num; exact (le_div_iff₀ hlog).2 (by simpa using hseed))
  have Xeq : X^2=N/logN := Real.sq_sqrt (by positivity)
  obtain ⟨d,hd,hD,hD',hmax⟩ := paper_period_max X1
  let K := (paperPeriod d:ℝ)
  let K' := (paperPeriod (d+1):ℝ)
  have hK : 1≤K := by dsimp [K]; exact_mod_cast paperPeriod_one_le hd
  have hK' : 1≤K' := by dsimp [K']; exact_mod_cast paperPeriod_one_le (by omega : 0<d+1)
  have hk : 0<K := by linarith
  have hk' : 0<K' := by linarith
  have eq : K'=2*K+1 := by unfold K K'; exact_mod_cast paperPeriod_succ d
  have oo (e : ℕ) : paperV p n e=N/(paperPeriod e:ℝ)^2 := by
    unfold paperV N
    rw [div_div, mul_comm (29:ℝ)]
  have D : logN≤paperV p n d := by
    rw [oo]
    apply (le_div_iff₀ (by positivity : 0<K^2)).2
    have H := pow_le_pow_left₀ hk.le hD 2
    rw [Xeq] at H
    simpa only [mul_comm] using (le_div_iff₀ hlog).1 H
  have D' : paperV p n (d+1)<logN := by
    rw [oo]
    apply (div_lt_iff₀ (by positivity : 0<K'^2)).2
    have H := pow_lt_pow_left₀ hD' (by linarith : 0≤X) (by decide : 2≠0)
    rw [Xeq] at H
    simpa only [mul_comm] using (div_lt_iff₀ hlog).1 H
  have co : K'^2≤9*K^2 := by
    have H : K'≤3*K := by linarith
    have E := pow_le_pow_left₀ hk'.le H 2
    nlinarith
  have upp : paperV p n d <144*Real.log n := by
    rw [oo]
    apply (div_lt_iff₀ (by positivity : 0<K^2)).2
    rw [oo] at D'
    have A := (div_lt_iff₀ (by positivity : 0<K'^2)).1 D'
    have B := mul_le_mul_of_nonneg_left co hlog.le
    dsimp [logN] at A B
    nlinarith
  refine ⟨d,hd,D,upp,D',?_⟩
  intro e he hE
  apply hmax e
  let X' := (paperPeriod e:ℝ)
  have he0 : 0<X' := by dsimp [X']; exact_mod_cast (show 0<paperPeriod e by have := paperPeriod_one_le he; omega)
  rw [oo] at hE
  have H := (le_div_iff₀ (by positivity : 0<X'^2)).1 hE
  apply Real.le_sqrt_of_sq_le
  apply (le_div_iff₀ hlog).2
  simpa only [mul_comm] using H

theorem paper_first_binary_ge {v : ℝ} (hv : 1<v) :
    ∃ b : ℕ, 0<b ∧ v≤(2:ℝ)^b ∧ (2:ℝ)^b<2*v ∧
      ∀ b' : ℕ, v≤(2:ℝ)^b' → b≤b' := by
  obtain ⟨N,hN⟩ := exists_nat_gt v
  have H : ∃ b : ℕ, v≤(2:ℝ)^b := by
    have T := Nat.lt_pow_self (n:=N) (a:=2) (by decide : 1<2)
    have C : (N:ℝ)<(2:ℝ)^N := by exact_mod_cast T
    exact ⟨N,(hN.trans C).le⟩
  let b := Nat.find H
  have hb : v≤(2:ℝ)^b := Nat.find_spec H
  have hb0 : 0<b := by
    by_contra! h
    have E : b=0 := by omega
    rw [E,pow_zero] at hb
    linarith
  have H' : (2:ℝ)^(b-1)<v := lt_of_not_ge (Nat.find_min H (show b-1<b by omega))
  have hb' : (2:ℝ)^b<2*v := by
    have E : b-1+1=b := by omega
    nth_rw 1 [←E]
    rw [pow_succ]
    linarith
  exact ⟨b,hb0,hb,hb',fun b' hh => Nat.find_min' H hh⟩

#print axioms paper_v_period_prescription
#print axioms paper_first_binary_ge
end CenteredCubeSqrt
