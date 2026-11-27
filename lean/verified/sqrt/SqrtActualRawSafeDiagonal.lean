import SqrtRawDiagonalSafe

namespace CenteredCubeSqrt
open MeasureTheory Set
open scoped Interval BigOperators
set_option maxHeartbeats 900000
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem actual_raw_correlation_at_safe_length {b d : ℕ} [NeZero (2^d-1)]
    (hd : 0<d) (g : (LabelField d)ˣ) (hg : orderOf g=2^d-1) {t : Fin b → LabelField d}
    (ht : LinearIndependent (ZMod 2) t) (hdim : 2*b≤d)
    {L : ℝ} (hK : 18≤(2^d-1:ℕ)) (hL : L∈Icc (10/9:ℝ) (11/9))
    (hSafe : actualSafeLifts hd g hg t L) :
    let K := ((2^d-1:ℕ):ℝ)
    let f := ordinalPhaseLabel hd g hg t
    |rawCorrelation f (K*L)| ≤ 1/(12*((2:ℝ)^b)^2)+1/(2*K) := by
  let f := ordinalPhaseLabel hd g hg t
  let K := ((2^d-1:ℕ):ℝ)
  let k : ℤ := ⌊K*L⌋
  let θ := K*L-(k:ℝ)
  have hu : (k:ℝ)≤K*L := Int.floor_le _
  have hl : K*L<(k:ℝ)+1 := Int.lt_floor_add_one _
  have hθ : θ∈Icc (0:ℝ) 1 := ⟨by dsimp [θ]; linarith,by dsimp [θ]; linarith⟩
  have h1 : |(k:ℝ)-K*L|<2 := abs_lt.mpr ⟨by linarith,by linarith⟩
  have h2 : |((k+1:ℤ):ℝ)-K*L|<2 := by push_cast; exact abs_lt.mpr ⟨by linarith,by linarith⟩
  obtain ⟨e1,e2⟩ := actualSafeLifts_regular_coarse hd g hg hK hL hSafe k h1
  obtain ⟨e3,e4⟩ := actualSafeLifts_regular_coarse hd g hg hK hL hSafe (k+1) h2
  push_cast at e3 e4
  change |rawCorrelation f (K*L)| ≤ _
  rw [show K*L=(k:ℝ)+θ by dsimp [θ]; ring]
  exact actual_raw_regular_correlation_bound hd g hg ht hdim k hθ e1 e2 e3 e4

theorem actual_raw_zero_correlation_close {b d : ℕ} [NeZero (2^d-1)]
    (hd : 0<d) (g : (LabelField d)ˣ) (hg : orderOf g=2^d-1) {t : Fin b → LabelField d}
    (ht : LinearIndependent (ZMod 2) t) (hdim : 2*b≤d)
    {L : ℝ} (hK : 18≤(2^d-1:ℕ)) (hL : L∈Icc (10/9:ℝ) (11/9))
    (hSafe : actualSafeLifts hd g hg t L) :
    let K := ((2^d-1:ℕ):ℝ)
    let f := ordinalPhaseLabel hd g hg t
    |rawCorrelation f 0-1/6| ≤ 1/(12*((2:ℝ)^b)^2)+1/(2*K) := by
  let f := ordinalPhaseLabel hd g hg t
  let K := ((2^d-1:ℕ):ℝ)
  let B := (2:ℝ)^b
  let k : ℤ := ⌊K*L⌋
  let ε := 1/(12*B^2)
  let w := ∫ r in (0:ℝ)..1,(cellPrimitive (labelCellMidpoint (0:Fin (2^b))) r)^2
  have hpos : 0<(2^d-1:ℕ) := by omega
  have hk0 : 0<K := by dsimp [K]; exact_mod_cast hpos
  have hu : (k:ℝ)≤K*L := Int.floor_le _
  have hl : K*L<(k:ℝ)+1 := Int.lt_floor_add_one _
  have h1 : |(k:ℝ)-K*L|<2 := abs_lt.mpr ⟨by linarith,by linarith⟩
  obtain ⟨e1,e2⟩ := actualSafeLifts_regular_coarse hd g hg hK hL hSafe k h1
  have E := actual_raw_zero_correlation_exact hd g hg ht (k:ZMod (2^d-1)) e1 e2 hdim
  have hq : (2:ℝ)^d=K+1 := by
    have h : 0<(2^d:ℕ) := by positivity
    dsimp [K]
    exact_mod_cast (Nat.sub_add_cancel (show 1≤(2^d:ℕ) by omega)).symm
  have hB : 1≤B := by dsimp [B]; exact one_le_pow₀ (by norm_num)
  have hε0 : 0≤ε := by dsimp [ε]; positivity
  have hε : ε≤1/6 := by
    unfold ε
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [pow_le_pow_left₀ (show (0:ℝ)≤1 by norm_num) hB 2]
  have hw : w≤1/3 := by exact label_zero_energy_le_third (B:=2^b) (by positivity)
  have hw0 : 0≤w := intervalIntegral.integral_nonneg_of_forall (by norm_num) (fun _ => sq_nonneg _)
  change |rawCorrelation f 0-1/6|≤ε+1/(2*K)
  change rawCorrelation f 0=((2:ℝ)^d/K)*(1/6-ε)-(1/K)*w at E
  rw [E,hq,show ((K+1)/K)*(1/6-ε)-(1/K)*w-1/6 =
    -ε+(1/K)*((1/6-ε)-w) by field_simp; ring]
  refine (abs_add_le _ _).trans ?_
  rw [abs_neg,abs_of_nonneg hε0,abs_mul,abs_of_nonneg (by positivity : 0≤1/K)]
  have hn : |(1/6-ε)-w|≤1/2 := abs_le.mpr ⟨by linarith,by linarith⟩
  have hn' := mul_le_mul_of_nonneg_left hn (show 0≤1/K by positivity)
  rw [show 1/K*(1/2:ℝ)=1/(2*K) by ring] at hn'
  linarith

theorem rawWindow_diagonal_bound_from_corr {B K : ℕ} [NeZero K]
    (f : ZMod K → Fin B) (L X : ℝ)
    (h0 : |rawCorrelation f 0-1/6|≤1/(12*X^2)+1/(2*(K:ℝ)))
    (hL : |rawCorrelation f ((K:ℝ)*L)|≤1/(12*X^2)+1/(2*(K:ℝ))) :
    |periodInner (actualRawWindow f L) (actualRawWindow f L)-1/3| ≤
      1/(3*X^2)+2/(K:ℝ) := by
  let c := rawCorrelation f 0-1/6
  let e := rawCorrelation f ((K:ℝ)*L)
  have hEq := rawWindow_covariance_from_correlation f L L
  rw [show (K:ℝ)*(L-L)/2=0 by ring,show (K:ℝ)*(L+L)/2=(K:ℝ)*L by ring] at hEq
  rw [hEq]
  have q : 2*rawCorrelation f 0-2*rawCorrelation f ((K:ℝ)*L)-1/3=2*c+(-(2*e)) := by
    unfold c e
    ring
  rw [q]
  refine (abs_add_le _ _).trans ?_
  rw [abs_neg,abs_mul,abs_mul,abs_of_nonneg (by norm_num : 0≤(2:ℝ))]
  have h0' : |c|≤1/(12*X^2)+1/(2*(K:ℝ)) := h0
  have hL' : |e|≤1/(12*X^2)+1/(2*(K:ℝ)) := hL
  calc
    _ ≤ 2*(1/(12*X^2)+1/(2*(K:ℝ)))+2*(1/(12*X^2)+1/(2*(K:ℝ))) := by linarith
    _ = _ := by ring

theorem actual_raw_safe_diagonal {b d : ℕ} [NeZero (2^d-1)]
    (hd : 0<d) (g : (LabelField d)ˣ) (hg : orderOf g=2^d-1) {t : Fin b → LabelField d}
    (ht : LinearIndependent (ZMod 2) t) (hdim : 2*b≤d)
    {L : ℝ} (hK : 18≤(2^d-1:ℕ)) (hL : L∈Icc (10/9:ℝ) (11/9))
    (hSafe : actualSafeLifts hd g hg t L) :
    let K := ((2^d-1:ℕ):ℝ)
    let f := ordinalPhaseLabel hd g hg t
    |periodInner (actualRawWindow f L) (actualRawWindow f L)-1/3| ≤
      1/(3*((2:ℝ)^b)^2)+2/K := by
  exact rawWindow_diagonal_bound_from_corr (ordinalPhaseLabel hd g hg t) L ((2:ℝ)^b)
    (actual_raw_zero_correlation_close hd g hg ht hdim hK hL hSafe)
    (actual_raw_correlation_at_safe_length hd g hg ht hdim hK hL hSafe)

#print axioms actual_raw_safe_diagonal
end CenteredCubeSqrt
