import ActualPairFromKernel
import ActualRetainedPairOverlap

namespace CenteredCubeSqrt
open MeasureTheory ProbabilityTheory Set Filter MvPolynomial CubeBrownian CubeSqrtProbability CubeSqrtOverlap Finset
open scoped ProbabilityTheory Interval
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
set_option maxHeartbeats 2600000

theorem actual_retained_overlap_from_packet_kernel {b d : ℕ} [NeZero (2^d-1)]
    (hd : 0<d) (g : (LabelField d)ˣ) (hg : orderOf g=2^d-1) (t : Fin b → LabelField d)
    (M : ℕ) {δ : ℝ} (hδ : 0<δ)
    (hδB : δ<1/((((2^b:ℕ):ℝ))*(((2^d-1:ℕ):ℝ))))
    (hK : 18≤(2^d-1:ℕ)) {n : ℕ} (hn : 0<n) {p u v C h : ℝ} (hP : 0<p) (hu : 0<u) (huv : u^2=v)
    (hv : v=(n:ℝ)*(p/(((2^d-1:ℕ):ℝ)))^2*(9/29))
    (ha : 7*p/(((2^d-1:ℕ):ℝ))≤1/8)
    (hC : v*actualPairRelativeError ((2:ℝ)^b) (((2^d-1:ℕ):ℝ)) M δ≤C)
    (hFac : 4*v/5≤(v-C)/(1+7*p/(((2^d-1:ℕ):ℝ))))
    (hNearErr : 8*v*actualPairNearError ((2:ℝ)^b) (((2^d-1:ℕ):ℝ)) M δ≤2)
    (N : ℕ) (P A D : ℝ) (hP0 : 0<P) (hA : 0≤A) (hD : 0<D)
    (hSpacing : (N:ℝ)*A+D≤P) (hRoom : (N:ℝ)*A≤(((2^d-1:ℕ):ℝ))*v/18)
    (R : Finset ℕ) (hR : R.Nonempty)
    (hSub : R ⊆ range (rawPacketCount ((((2^d-1:ℕ):ℝ))*v/18) ((N:ℝ)*A) P))
    (hSafeNodes : ∀ i∈R, ∀ a : Fin (N+1),
       let L := paperPacketLength (((2^d-1:ℕ):ℝ)) v P A i a.1
       L∈Icc (10/9:ℝ) (11/9) ∧ actualSafeLifts hd g hg t L)
    (hKernel : ∀ i j : ℕ, i∈R → j∈R → ∀ a b' : Fin (N+1),
      let K := ((2^d-1:ℕ):ℝ)
      let B := (2:ℝ)^b
      let f := ordinalPhaseLabel hd g hg t
      let L := paperPacketLength K v P A i a.1
      let J := paperPacketLength K v P A j b'.1
      let κ := actualNormalizedGram f M δ L J
      let τ := K*|J-L|/2
      (0<actualWitnessGram f M δ L L ∧
        |actualWitnessGram f M δ L L/((27/29)*L^2/3)-1|≤actualPairRelativeError B K M δ) ∧
      (0<actualWitnessGram f M δ J J ∧
        |actualWitnessGram f M δ J J/((27/29)*J^2/3)-1|≤actualPairRelativeError B K M δ) ∧
      (τ≤1/8 → (174/121)*τ-8*actualPairNearError B K M δ≤1-κ) ∧
      -(1/2:ℝ)≤κ ∧ (1/8≤τ → 1/5≤1-κ)) :
    let K := ((2^d-1:ℕ):ℝ)
    let f := ordinalPhaseLabel hd g hg t
    let B := rawPacketCount (K*v/18) ((N:ℝ)*A) P
    let U (i : ℕ) := ⋃ a : Fin (N+1),
      actualPaperScaleEvent f M n p δ h (paperPacketLength K v P A i a.1)
    let c : ℝ := 174/121/8
    u*Real.exp h*(∑ i ∈ R, ∑ j ∈ R.filter (fun j => i<j), (actualPaperProductLaw n).real (U i∩U j))/(R.card:ℝ)
      ≤ ((N:ℝ)+1)^2*(actualPairPrefactor*Real.exp (1/4)*Real.exp (-c*D)/(1-Real.exp (-c*P))
        +(B:ℝ)*(actualPairPrefactor*Real.exp (-v/25))) := by
  classical
  let K := ((2^d-1:ℕ):ℝ)
  let f := ordinalPhaseLabel hd g hg t
  let B := rawPacketCount (K*v/18) ((N:ℝ)*A) P
  let L (i : ℕ) (a : Fin (N+1)) := paperPacketLength K v P A i a.1
  let E (i : ℕ) (a : Fin (N+1)) := actualPaperScaleEvent f M n p δ h (L i a)
  let c : ℝ := 174/121/8
  let offset (a : Fin (N+1)) := (a.1:ℝ)*A
  let τ (i j : ℕ) (a b : Fin (N+1)) := K * |L j b-L i a|/2
  let G := fun i j a b => τ i j a b≤1/8
  have hzK : 0<K := by dsimp [K]; exact_mod_cast (show 0<(2^d-1:ℕ) by omega)
  have hzv : 0<v := huv ▸ sq_pos_of_pos hu
  have hRB : R⊆range B := hSub
  have hSafe (i : ℕ) (hi : i∈R) (a : Fin (N+1)) : actualSafeLifts hd g hg t (L i a) :=
    (hSafeNodes i hi a).2
  have hValid (i : ℕ) (hi : i∈R) (a : Fin (N+1)) :
      L i a ∈ Icc (10/9:ℝ) (11/9) :=
    (hSafeNodes i hi a).1
  have hOff₀ (a : Fin (N+1)) : 0≤offset a := by unfold offset; positivity
  have hOff₁ (a : Fin (N+1)) : offset a≤(N:ℝ)*A := by
    have hN : (a.1:ℝ)≤N := by exact_mod_cast (show a.1≤N by omega)
    exact mul_le_mul_of_nonneg_right hN hA
  have hIdentity (i j : ℕ) (hi : i∈R) (hj : j∈R) (hij : i<j) (a b : Fin (N+1)) :
      v*τ i j a b = (j:ℝ)*P+offset b-((i:ℝ)*P+offset a) := by
    obtain ⟨hG,hG0,_⟩ := paper_packet_tau_domain K v P A D hzK hzv hP0 hA hD N hSpacing hRoom
      i j (hRB hi) (hRB hj) hij a b
    have hr : 0≤L j b-L i a := by
      apply nonneg_of_mul_nonneg_left _ hzK
      change 0<K*(L j b-L i a)/2 at hG0
      linarith
    change v*(K*|L j b-L i a|/2) = _
    rw [abs_of_nonneg hr]
    change K*(L j b-L i a)/2 = _ at hG
    rw [hG]
    field_simp [hzv.ne']
    unfold offset
    ring
  have hPair (i j : ℕ) (hi : i∈R) (hj : j∈R) (a b : Fin (N+1)) :=
    actual_pair_probability_from_kernel hd g hg t M hδ hδB hK (hValid i hi a) (hValid j hj b)
       (hKernel i j hi hj a b) hn hP hu huv hv ha hC hFac hNearErr (h:=h)
  have hh := retained_packet_overlap_normalized (actualPaperProductLaw n) B R hRB hR E
    (u*Real.exp h) P ((N:ℝ)*A) D c (actualPairPrefactor*Real.exp (1/4))
    (actualPairPrefactor*Real.exp (-v/25)) (by positivity) hP0 (by unfold c; norm_num)
    (mul_nonneg actual_pairPrefactor_nonneg (Real.exp_nonneg _))
    (mul_nonneg actual_pairPrefactor_nonneg (Real.exp_nonneg _)) hSpacing offset hOff₀ hOff₁ G
    (by
      intro i hi j hj hij a b hnear
      have H := (hPair i j hi hj a b).1 hnear
      change u*Real.exp h*(actualPaperProductLaw n).real (E i a∩E j b) ≤
         actualPairPrefactor*Real.exp (1/4)*Real.exp (-c*(v*τ i j a b)) at H
      rwa [hIdentity i j hi hj hij a b] at H)
    (by
      intro i hi j hj _ a b hfar
      exact (hPair i j hi hj a b).2 (le_of_lt (not_le.mp hfar)))
  simpa only [Fintype.card_fin,Nat.cast_add,Nat.cast_one] using hh

#print axioms actual_retained_overlap_from_packet_kernel
end CenteredCubeSqrt
