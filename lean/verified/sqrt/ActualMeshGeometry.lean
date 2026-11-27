import WeightedModulusTail
import DriftedBrownianMaximum
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
namespace CubeBrownian

noncomputable def cellLeft (A : ℝ≥0) (i : ℕ) : ℝ≥0 := (i:ℝ≥0)*A

theorem cellLeft_succ (A : ℝ≥0) (i : ℕ) : cellLeft A (i+1) = cellLeft A i+A := by
  unfold cellLeft
  push_cast
  ring

theorem exists_uniformCell {N : ℕ} (hN : 0 < N) {A t : ℝ≥0} (hA : 0 < A)
    (ht : t ≤ cellLeft A N) : ∃ i : Fin N, ∃ s ≤ A, t = cellLeft A i+s := by
  let q : ℝ := (t:ℝ)/(A:ℝ)
  have hAr : 0 < (A:ℝ) := by exact_mod_cast hA
  have hq : q ≤ N := by
    apply (div_le_iff₀ hAr).2
    exact_mod_cast ht
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  let k := ⌊q⌋₊
  have hkn : k ≤ N := Nat.floor_le_of_le hq
  let i : Fin N := ⟨min k (N-1),by omega⟩
  have hlow : cellLeft A i ≤ t := by
    have hp : ((i:ℕ):ℝ) ≤ q :=
      (Nat.cast_le.mpr (min_le_left _ _)).trans (Nat.floor_le hq0)
    have h := (le_div_iff₀ hAr).mp hp
    exact_mod_cast h
  have hu : t ≤ cellLeft A i+A := by
    have hQi : q ≤ ((i:ℕ):ℝ)+1 := by
      by_cases hk : k<N
      · change q ≤ ((min k (N-1):ℕ):ℝ)+1
        rw [min_eq_left (by omega : k ≤ N-1)]
        exact (Nat.lt_floor_add_one q).le
      · have he : ((i:ℕ):ℝ)+1 = (N:ℝ) := by
          exact_mod_cast (show min k (N-1)+1 = N by omega)
        exact he.symm ▸ hq
    have h := (div_le_iff₀ hAr).mp hQi
    have he : (((i:ℕ):ℝ)+1)*(A:ℝ) = (cellLeft A i:ℝ)+(A:ℝ) := by
      simp [cellLeft,add_mul]
    rw [he] at h
    exact_mod_cast h
  refine ⟨i,t-cellLeft A i,?_ ,?_⟩
  · exact tsub_le_iff_right.mpr (by simpa only [add_comm] using hu)
  · exact (add_tsub_cancel_of_le hlow).symm

theorem measurable_finite_real_sup {Ω ι : Type*} [MeasurableSpace Ω] [Finite ι] [Nonempty ι]
    (f : ι → Ω → ℝ) (hf : ∀ i, Measurable (f i)) : Measurable (fun w ↦ ⨆ i, f i w) := by
  apply measurable_of_Ioi
  intro a
  have h : {w | a < ⨆ i, f i w} = ⋃ i, {w | a < f i w} := by
    ext w
    simp only [mem_ofPred_eq,mem_iUnion]
    exact lt_ciSup_iff (finite_range _).bddAbove
  change MeasurableSet {w | a < ⨆ i, f i w}
  rw [h]
  exact .iUnion (fun i ↦ measurableSet_lt measurable_const (hf i))

noncomputable def meshGridMax {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (A : ℝ≥0) (N : ℕ) (w : Ω) : ℝ :=
  ⨆ i : Fin (N+1), driftedCentered B w (cellLeft A i)

noncomputable def meshCellModulus {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (left A : ℝ≥0) : Ω → ℝ :=
  sampledSup (fun k w ↦ |driftedCentered B w (left+gridSample A k)-driftedCentered B w left|)

noncomputable def meshModulus {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (A : ℝ≥0) (N : ℕ) (w : Ω) : ℝ :=
  ⨆ i : Fin N, meshCellModulus B (cellLeft A i) A w

theorem measurable_meshGridMax {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (hmB : ∀ t, Measurable (B t)) (A : ℝ≥0) (N : ℕ) :
    Measurable (meshGridMax B A N) :=
  measurable_finite_real_sup _ (fun i ↦
    (measurable_const.mul ((hmB (cellLeft A i)).sub (hmB 0))).sub measurable_const)

theorem measurable_meshCellModulus {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (hmB : ∀ t, Measurable (B t)) (left A : ℝ≥0) :
    Measurable (meshCellModulus B left A) := by
  have hm (t : ℝ≥0) : Measurable (fun w ↦ driftedCentered B w t) :=
    (measurable_const.mul ((hmB t).sub (hmB 0))).sub measurable_const
  exact measurable_sampledSup _ (fun k ↦ ((hm (left+gridSample A k)).sub (hm left)).abs)

theorem measurable_meshModulus {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (hmB : ∀ t, Measurable (B t)) (A : ℝ≥0) (N : ℕ) (hN : 0 < N) :
    Measurable (meshModulus B A N) := by
  let _ : Nonempty (Fin N) := ⟨⟨0,hN⟩⟩
  exact measurable_finite_real_sup _ (fun _ ↦ measurable_meshCellModulus B hmB _ A)

theorem meshCellModulus_spec {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (w : Ω)
    (hC : Continuous (B · w)) (left A : ℝ≥0) (hA : 0 < A) (x : ℝ) :
    x < meshCellModulus B left A w ↔
      ∃ s ≤ A, x < |driftedCentered B w (left+s)-driftedCentered B w left| := by
  let F := fun w' (s : ℝ≥0) ↦ |driftedCentered B w' (left+s)-driftedCentered B w' left|
  have hc : Continuous (F w) := by
    dsimp [F,driftedCentered,centeredScaled]
    fun_prop
  have h0 : F w 0 = 0 := by simp [F]
  exact ((sampledSup_grid_spec F w hA hc h0).2 x).trans (dyadicHits_iff_exists hA x _ hc)

theorem meshGrid_path_bounds {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (w : Ω)
    (hC : Continuous (B · w)) (A : ℝ≥0) (hA : 0 < A) (N : ℕ) (hN : 0 < N) :
    let M := driftedBrownianGridMax B (cellLeft A N) w
    let G := meshGridMax B A N w
    let U := meshModulus B A N w
    0 ≤ M ∧ G ≤ M ∧ M ≤ G+U ∧
      ∃ i : Fin (N+1), G = driftedCentered B w (cellLeft A i) := by
  dsimp only
  let _ : Nonempty (Fin N) := ⟨⟨0,hN⟩⟩
  let f := driftedCentered B w
  let T := cellLeft A N
  let M := driftedBrownianGridMax B T w
  let G := meshGridMax B A N w
  let U := meshModulus B A N w
  have hT : 0 < T := by unfold T cellLeft; positivity
  have hf : Continuous f := (continuous_const.mul (hC.sub continuous_const)).sub continuous_subtype_val
  have hf0 : f 0 = 0 := by simp [f,driftedCentered,centeredScaled_zero]
  have hspec := sampledSup_grid_spec (driftedCentered B) w hT hf hf0
  have hm (x : ℝ) : x < M ↔ ∃ s ≤ T, x < f s :=
    (hspec.2 x).trans (dyadicHits_iff_exists hT x f hf)
  have hle (t : ℝ≥0) (ht : t ≤ T) : f t ≤ M := by
    by_contra! h
    exact (lt_irrefl _) ((hm M).mpr ⟨t,ht,h⟩)
  have hleft (i : Fin (N+1)) : cellLeft A i ≤ T := by
    unfold T cellLeft
    gcongr
    exact Nat.le_of_lt_succ i.isLt
  have hG : G ≤ M := ciSup_le (fun i ↦ hle _ (hleft i))
  have hUbound (i : Fin N) (s : ℝ≥0) (hs : s ≤ A) :
      |f (cellLeft A i+s)-f (cellLeft A i)| ≤ U := by
    let V := meshCellModulus B (cellLeft A i) A w
    have hV : |f (cellLeft A i+s)-f (cellLeft A i)| ≤ V := by
      by_contra! h
      exact (lt_irrefl _) ((meshCellModulus_spec B w hC _ A hA V).mpr ⟨s,hs,h⟩)
    exact hV.trans (le_ciSup (finite_range (fun i : Fin N ↦ meshCellModulus B (cellLeft A i) A w)).bddAbove i)
  have hupper (t : ℝ≥0) (ht : t ≤ T) : f t ≤ G+U := by
    obtain ⟨i,s,hs,rfl⟩ := exists_uniformCell hN hA ht
    have hi : f (cellLeft A i) ≤ G := le_ciSup
      (finite_range (fun i : Fin (N+1) ↦ f (cellLeft A i))).bddAbove i.castSucc
    have h := (le_abs_self (f (cellLeft A i+s)-f (cellLeft A i))).trans (hUbound i s hs)
    linarith only [hi,h]
  have hM : M ≤ G+U := by
    by_contra! h
    obtain ⟨t,ht,hlt⟩ := (hm (G+U)).mp h
    exact (not_lt_of_ge (hupper t ht)) hlt
  refine ⟨hspec.1,hG,hM,?_⟩
  obtain ⟨i,hi⟩ := exists_eq_ciSup_of_finite (f := fun i : Fin (N+1) ↦ f (cellLeft A i))
  exact ⟨i,hi.symm⟩
end CubeBrownian
#print axioms CubeBrownian.meshGrid_path_bounds
