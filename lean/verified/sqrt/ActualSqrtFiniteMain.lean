import ActualPacketCompatibility
import ActualSqrtFinalScalar
import CoherentSourceWithChoice
import SqrtActualPacketFirstSum

open Filter Set MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology BigOperators
namespace CenteredCubeSqrt
open CubeBrownian CubeSqrtProbability CubeSqrtOverlap
set_option maxHeartbeats 3000000
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem paper_actual_finite_eventual_coefficient
    {p η b : ℝ} (hp : 0<p) (hp1 : p<1) (hη : 0<η) (hb : 0<b)
    (T w : ℕ) (hT : 2≤T) (hw : T^2+4≤w)
    (hMesh : ∀ L∈paperScaleWindow, (T:ℝ)*(29/(9*L^2)-η/2) ≤ actualSmoothedGridMean T w L)
    (hbc : b < paperLowerCoeff p η T) :
    ∀ᶠ n : ℕ in atTop, ENNReal.ofReal (b*Real.sqrt (n:ℝ)) ≤ CenteredCube.weakConstant n := by
  classical
  let A : ℝ := 1/(T:ℝ)^2
  let N : ℕ := T^3
  let D : ℝ := paperPairPacketGap T
  let P : ℝ := (N:ℝ)*A+D
  obtain ⟨hA,hw4,hAQ,hTA⟩ := paper_packet_width_value T w hw hT
  have hTA : (N:ℝ)*A=T := hTA
  have hT0 : 0<(T:ℝ) := by exact_mod_cast (show 0<T by omega)
  have hD : 0<D := paper_pair_packet_gap_positive (by exact_mod_cast (show 1<T by omega))
  have hP : 0<P := by unfold P; positivity
  have hEq : P = paperMeshPeriod T := by simpa only [P, paperMeshPeriod, hTA, D]
  obtain ⟨d,l,R,X,hv,hGrowth,hAmpV,hv2,hr,hCount,hStep,hData,hChoice,hFull⟩ :=
    paper_coherent_certified_source_with_choice hp hw4 hA hD N
  let v n := paperV p n (d n)
  let K n := (paperPeriod (d n):ℝ)
  let score n i := paperPacketNormalizedProb p P A N n (d n) i (X n)
  have hK : Tendsto K atTop atTop := by simpa only [pow_zero,div_one] using hGrowth 0
  have hDataW : ∀ᶠ n : ℕ in atTop,
      let B := (2:ℝ)^(l n)
      let M := paperMeshM (v n)
      let r := paperKernelRelError B (K n) (paperAtomicCrossSmoothing w (K n) B (v n) M) M
      v n < 144*Real.log (n:ℝ) ∧ v n*r ≤ 2/(w:ℝ) ∧
        CertifiedActualFamily p w P A n (l n) (d n) N (R n) (X n) :=
    hData.mono (fun _ H => ⟨H.2.2.1,H.2.2.2.1,H.2.2.2.2.2⟩)
  have hφ : 0<φ 0 := by rw [paper_phi_zero]; positivity
  have hWin := actual_packet_winner_uniform (P := P) hp hw4 hA hAQ
    (N := N) (b := l) (d := d) (R := R) (X := X) hK hv hAmpV hv2 hDataW
    (φ 0*(T:ℝ)*η/2) (by positivity)
  have hScore : ∀ᶠ n in atTop, ∀ i∈R n,
      (φ 0*(T:ℝ)*(29/9))/(paperPacketLength (paperPeriod (d n)) (v n) P A i 0)^2 -
      φ 0*(T:ℝ)*η ≤ score n i := by
    filter_upwards [hWin,hData] with n hwin hn i hi
    let L := paperPacketLength (paperPeriod (d n)) (v n) P A i 0
    have hAbs := hwin i hi
    change |score n i - φ 0*canonicalFiniteGridExp (paperPacketBoxGrid w A hw4 hA N)
      (paperPacketLambda L)| < φ 0*(T:ℝ)*η/2 at hAbs
    have hRef := canonical_box_grid_reference_eq T w hw hT L hw4 hA
    change canonicalFiniteGridExp (paperPacketBoxGrid w A hw4 hA N)
      (paperPacketLambda L) = actualSmoothedGridMean T w L at hRef
    rw [hRef,abs_lt] at hAbs
    obtain ⟨_,_,_,_,_,_,_,hLoc,_,_,_⟩ := hn.2.2.2.2.2
    have hL : L∈paperScaleWindow := (hLoc i hi).2.1
    have hS := mul_le_mul_of_nonneg_left (hMesh L hL) hφ.le
    have he : φ 0*(T:ℝ)*(29/9)/L^2-φ 0*(T:ℝ)*η =
        φ 0*((T:ℝ)*(29/(9*L^2)-η/2))-φ 0*(T:ℝ)*η/2 := by
      rw [show (29:ℝ)/(9*L^2)=(29/9)/L^2 from (div_div _ _ _).symm]
      ring
    change φ 0*(T:ℝ)*(29/9)/L^2-φ 0*(T:ℝ)*η ≤ score n i
    rw [he]
    linarith only [hAbs.1,hS]
  have hd : ∀ᶠ n in atTop, 0<d n ∧ 16*Real.log n≤v n ∧ v n<144*Real.log n := by
    filter_upwards [hData] with n H
    obtain ⟨_,_,_,hD,_,_⟩ := H.2.2.2.2.1
    exact ⟨hD,H.2.1,H.2.2.1⟩
  let q := (paperLowerCoeff p η T-b)/4
  have hq : 0<q := by dsimp [q]; linarith
  have hFirst := actual_packet_score_first_sum (w := (w:ℝ)) hp hP hA.le
    (show 0 ≤ φ 0*(T:ℝ)*(29/9) by positivity)
    (d := d) (b := l) (N := N) (R := R) score hd
    (hData.mono fun _ H => H.2.2.2.2.1) hScore q hq
  have hOverlap := paper_r23_eventually_global_overlap hp hw4 hA hD N d l R hGrowth hCount hChoice q hq
  have hVoverK : Tendsto (fun n => v n/K n) atTop (𝓝 0) := by
    simpa [K,v,Function.comp_def,inv_div] using (tendsto_inv_atTop_zero.comp (hGrowth 1))
  have hcoarse : ∀ᶠ n in atTop, (p/K n)*(9*(paperMeshM (v n):ℝ)) ≤ (1-p)/2 := by
    have hh := hVoverK.const_mul (9*p)
    rw [mul_zero] at hh
    filter_upwards [hK.eventually_gt_atTop 0,hData,
      hh.eventually_lt_const (by linarith : (0:ℝ)<(1-p)/2)] with n hnK H hq'
    have hmm := H.2.2.2.2.1.1.mesh_le_v
    calc
      _ ≤ (p/K n)*(9*v n) := by gcongr
      _ = (9*p)*(v n/K n) := by ring
      _ ≤ _ := hq'.le
  have hretT : Tendsto (fun n : ℕ => (b+q)*(1-1/(n:ℝ)^2)^n) atTop (𝓝 (b+q)) := by
    simpa only [mul_one] using CenteredCube.truncation_retention_tendsto.const_mul (b+q)
  have hret := hretT.eventually_const_lt (show b<b+q by linarith)
  filter_upwards [hFirst,hOverlap,hFull,hcoarse,hret,eventually_ge_atTop (1:ℕ)] with n h1 h2 hF hC hR hn
  obtain ⟨hdn,nz,g,hg,t,hX,hmp,_,_,_,hNodes,hG⟩ := hF
  letI : NeZero (2^d n-1) := nz
  let f := ordinalPhaseLabel hdn g hg t
  let δ := paperMeshDelta w (K n) (v n)
  let M := paperMeshM (v n)
  let h := v n/2-2
  let U := actualPaperPacketEvent f M n N p δ h (v n) P A
  have hδ : 0<δ := hmp.delta_positive
  have hK2 : 2≤(2^d n-1:ℕ) := by have hh := hmp.period_lower; unfold paperPeriod at hh; omega
  have hs : δ < 1/(((2^l n:ℕ):ℝ)*(((2^d n-1:ℕ):ℝ))) := by
    change δ < 1/(((2^l n:ℕ):ℝ)*K n)
    rw [show ((2^l n:ℕ):ℝ)=(2:ℝ)^l n by norm_cast]
    have hK0 : 0<K n := by dsimp [K]; exact_mod_cast (show 0<paperPeriod (d n) by have := hmp.period_lower; omega)
    refine hmp.delta_small.trans_le ?_
    apply div_le_div_of_nonneg_left (by norm_num) (mul_pos (by positivity) hK0)
    linarith [mul_pos (show 0<(2:ℝ)^l n by positivity) hK0]
  have hwit : ∀ i∈R n, ∀ x∈U i, ∃ L : ℝ, 0<L ∧ L≤2 ∧
      h < ∑ c, Real.log (1+actualWindowPerturbation f M p δ L (x c)) := by
    intro i hi x hx
    obtain ⟨j,hj⟩ := Set.mem_iUnion.1 hx
    let L := paperPacketLength (K n) (v n) P A i j
    have hm := (hNodes i hi j).1
    exact ⟨L,by linarith [hm.1],by linarith [hm.2],hj⟩
  let V (i : ℕ) := if i∈R n then U i else ∅
  have hV (i : ℕ) : MeasurableSet (V i) := by
    by_cases hi : i∈R n
    · unfold V
      rw [if_pos hi]
      apply MeasurableSet.iUnion
      intro j
      apply actualPaperScaleEvent_measurable _ _ _ _ _ hδ
      have hm : paperPacketLength (K n) (v n) P A i j ∈ paperScaleWindow :=
        (hNodes i hi j).1
      change 0 < paperPacketLength (K n) (v n) P A i j
      exact (by norm_num : (0:ℝ) < 10/9).trans_le hm.1
    · simp [V,hi]
  have hVeq (i : ℕ) (hi : i∈R n) : V i=U i := if_pos hi
  have hnorm (i : ℕ) (hi : i∈R n) :
      score n i = Real.sqrt (v n)*Real.exp h*(CenteredCube.sqrtCellLaw n).real (V i) := by
    unfold score paperPacketNormalizedProb
    rw [hX,hVeq i hi,←actual_paper_product_law_eq]
    let s (j : Fin (N+1)) (z : Fin n → ℝ) :=
      ∑ c, Real.log (1+actualWindowPerturbation f M p δ
        (paperPacketLength (K n) (v n) P A i j) (z c))
    change Real.sqrt (v n)*Real.exp h*(actualPaperProductLaw n).real {z | h < ⨆ j, s j z} =
      Real.sqrt (v n)*Real.exp h*(actualPaperProductLaw n).real (U i)
    have hset := paper_packet_prob_eq_union (n := n) (N := N) p (v n) P A δ f M i
    change {z | h < ⨆ j, s j z} = U i at hset
    rw [hset]
  have hsqrt : 0<Real.sqrt (v n) := Real.sqrt_pos.2 (by linarith [hmp.v_ge_four])
  have hfirst : (∑ i∈R n, score n i)/(Real.sqrt (v n)*Real.sqrt (n:ℝ)) =
      actualFirstCredit h (R n) V := by
    rw [Finset.sum_congr rfl hnorm,← Finset.mul_sum]
    unfold actualFirstCredit
    have hn0 : 0 < Real.sqrt (n:ℝ) := Real.sqrt_pos.2 (by exact_mod_cast (show 0<n by omega))
    field_simp [hsqrt.ne',hn0.ne']
  have hov : ActualPacketGlobalOverlapBound p w (v n) P A n (l n) (d n) N (R n)
      (paperPairGlobalEnvelope p P D N+q) := h2
  have hov' := hov hdn nz g hg t hNodes hG
  change Real.exp h*actualPaperOverlapSum n (R n) U / Real.sqrt (n:ℝ) ≤ _ at hov'
  have hovV : actualOverlapCredit h (R n) V =
      Real.exp h*actualPaperOverlapSum n (R n) U / Real.sqrt (n:ℝ) := by
    unfold actualOverlapCredit actualPaperOverlapSum
    rw [actual_paper_product_law_eq]
    have ee : (∑ i∈R n, ∑ j∈(R n).filter (fun j => i<j), (CenteredCube.sqrtCellLaw n).real (V i∩V j)) =
        ∑ i∈R n, ∑ j∈(R n).filter (fun j => i<j), (CenteredCube.sqrtCellLaw n).real (U i∩U j) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [hVeq i hi,hVeq j ((Finset.mem_filter.1 hj).1)]
    rw [ee]
    ring
  have hBonf := actual_packet_credits_bonferroni h (R n) V hV
  have hW := actual_packet_credit_to_weakConstant f M hn (by positivity) hK2 hp.le hp1 hδ hs
    hC (R n) V hV (fun i hi x hx => hwit i hi x (hVeq i hi ▸ hx))
  have h1' : (paperCp p/(2*P))*(φ 0*(T:ℝ)*(29/110-η/9))-q ≤
        actualFirstCredit h (R n) V := by
    rw [← hfirst]
    convert h1 using 1 <;> ring
  have hh : b+q ≤ actualUnionCredit h (R n) V := by
    rw [hovV] at hBonf
    have HQ : 4*q=paperLowerCoeff p η T-b := by unfold q; ring
    have HC : paperLowerCoeff p η T =
        (paperCp p/(2*P))*(φ 0*(T:ℝ)*(29/110-η/9))-
          paperPairGlobalEnvelope p P D N := by
      unfold paperLowerCoeff
      rw [←hEq]
    linarith only [h1',hov',hBonf,HQ,HC,hq]
  have hnR : (1:ℝ)≤n := by exact_mod_cast hn
  have hRetNN : 0≤(1-1/(n:ℝ)^2)^n := by
    exact pow_nonneg (sub_nonneg.2 ((div_le_one (by positivity)).2 (by nlinarith))) _
  exact (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
    (hR.le.trans (mul_le_mul_of_nonneg_right hh hRetNN)) (Real.sqrt_nonneg _))).trans hW

#print axioms paper_actual_finite_eventual_coefficient
end CenteredCubeSqrt
