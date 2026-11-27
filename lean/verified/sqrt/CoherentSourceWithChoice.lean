import SqrtCoherentPaperSource
import CertifiedSourceWithKernel

namespace CenteredCubeSqrt
open Set Filter MeasureTheory CubeSqrtOverlap
open scoped Topology BigOperators Interval
set_option maxHeartbeats 1300000

/-- The certified winner source and the original maximal period metadata have
a single coordinated witness. The final event is exactly the input needed by
the independent global-overlap theorem; no reselection of labels or packets. -/
theorem paper_coherent_certified_source_with_choice {p w A D : ℝ} (hp : 0<p) (hw : 4≤w)
    (hA : 0<A) (hD : 0<D) (N : ℕ) :
    let P := (N:ℝ)*A+D
    ∃ (d b : ℕ→ℕ) (R : ℕ→Finset ℕ) (X : ℕ→ℝ→ℝ→ℝ),
      let v (n : ℕ) := paperV p n (d n)
      let K (n : ℕ) := (paperPeriod (d n):ℝ)
      let amp (n : ℕ) := 7*|p|/K n
      let r (n : ℕ) :=
        let B := (2:ℝ)^(b n)
        let M := paperMeshM (v n)
        let E := paperAtomicCrossSmoothing w (K n) B (v n) M
        paperKernelRelError B (K n) E M
      Tendsto v atTop atTop ∧
      (∀ j : ℕ, Tendsto (fun n => K n/(v n)^j) atTop atTop) ∧
      (Tendsto (fun n => amp n*v n) atTop (𝓝 0)) ∧
      (Tendsto (fun n => (v n)^2/(n:ℝ)) atTop (𝓝 0)) ∧
      (Tendsto (fun n => v n*r n) atTop (𝓝 (87/(50*w)))) ∧
      (Tendsto (fun n => ((R n).card:ℝ)/(Real.sqrt (v n)*Real.sqrt (n:ℝ)))
        atTop (𝓝 (paperCp p/(18*P)))) ∧
      (Tendsto (fun n => (2*P/(K n*v n))*((R n).card:ℝ)) atTop (𝓝 (1/9))) ∧
      (∀ᶠ n in atTop, (R n).Nonempty ∧ 16*Real.log n≤v n ∧ v n<144*Real.log n ∧
        v n*r n≤2/w ∧
        ActualPacketChoice w (v n) P A (b n) (d n) N (R n) ∧
        CertifiedActualFamily p w P A n (b n) (d n) N (R n) (X n)) ∧
      (∀ᶠ n in atTop, (R n).Nonempty ∧
        16*Real.log n≤v n ∧ v n<144*Real.log n ∧
        paperV p n (d n+1)<16*Real.log n ∧
        (∀ e : ℕ, 0<e → 16*Real.log n≤paperV p n e → e≤d n) ∧
        ActualPacketChoice w (v n) P A (b n) (d n) N (R n)) ∧
      (∀ᶠ n in atTop, CertifiedActualFamilyWithKernel p w P A n (b n) (d n) N (R n) (X n)) := by
  let P := (N:ℝ)*A+D
  obtain ⟨d,b,R,hK,hC,hStep,h⟩ :=
    paper_all_integer_dimensions_actual_packets hp hw hA hD N
  let v (n : ℕ) := paperV p n (d n)
  let K (n : ℕ) := (paperPeriod (d n):ℝ)
  let r (n : ℕ) :=
    let B := (2:ℝ)^(b n)
    let M := paperMeshM (v n)
    let E := paperAtomicCrossSmoothing w (K n) B (v n) M
    paperKernelRelError B (K n) E M
  have hR : ∀ᶠ n in atTop, ActualPacketChoice w (v n) P A (b n) (d n) N (R n) :=
    h.mono fun _ H => H.2.2.2.2.2
  obtain ⟨X,hXfull⟩ := certified_actual_family_with_kernel_eventually hp hR
  have hX := hXfull.mono fun _ H => H.forget
  have hd : ∀ᶠ n in atTop, 0<d n ∧ 16*Real.log n≤v n ∧ v n<144*Real.log n := by
    filter_upwards [h,hR] with n H S
    obtain ⟨_,_,_,hd,_,_⟩ := S
    exact ⟨hd,H.2.1,H.2.2.1⟩
  have hv := paper_v_tendsto (v:=v) (hd.mono fun _ H => H.2.1)
  have hMeshes : ∀ᶠ n in atTop, PaperMeshParameters w (v n) (b n) (d n) :=
    hR.mono fun _ H => H.1
  have hRel : Tendsto (fun n => v n*r n) atTop (𝓝 (87/(50*w))) :=
    paper_actual_relative_error_scaled hw hMeshes hv (hK 4) (by simpa only [pow_one] using hK 1)
  have ws : 0<w := by linarith
  have hrr := hRel.eventually_lt_const (show (87:ℝ)/(50*w)<2/w by
    rw [←div_div]
    exact div_lt_div_of_pos_right (by norm_num) ws)
  refine ⟨d,b,R,X,hv,hK,actual_amp_scaled_tendsto hp d hd,actual_v_sq_over_n_tendsto d hd,
    hRel,hC,hStep,?_,h,hXfull⟩
  filter_upwards [h,hR,hX,hrr] with n H R' X' he
  exact ⟨H.1,H.2.1,H.2.2.1,he.le,R',X'⟩

#print axioms paper_coherent_certified_source_with_choice
end CenteredCubeSqrt
