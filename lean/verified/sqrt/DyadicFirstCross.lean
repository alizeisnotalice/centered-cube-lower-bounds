import DyadicGrid
import ContinuousGridReflection
open Filter Set
open scoped Topology NNReal
namespace CubeBrownian

noncomputable def dyadicIncrements (T : ℝ≥0) (r : ℕ) (f : ℝ≥0 → ℝ) :
    Fin (2^r) → ℝ := fun i ↦ f (dyadicT T r ((i:ℕ)+1)) - f (dyadicT T r i)

def dyadicHits (T : ℝ≥0) (r : ℕ) (a : ℝ) (f : ℝ≥0 → ℝ) : Prop :=
  ∃ k ≤ 2^r, a < f (dyadicT T r k)

theorem dyadicHits_mono (T : ℝ≥0) (a : ℝ) (f : ℝ≥0 → ℝ) :
    Monotone (fun r ↦ dyadicHits T r a f) := by
  apply monotone_nat_of_le_succ
  intro r
  rintro ⟨k,hk,h⟩
  refine ⟨2*k,?_,by rwa [dyadicT_refine]⟩
  rw [pow_succ,mul_comm (2^r)]
  exact Nat.mul_le_mul_left 2 hk

theorem dyadicHits_iff_prefix (T : ℝ≥0) (r : ℕ) (a : ℝ) (ha : 0 ≤ a)
    (f : ℝ≥0 → ℝ) (hf : f 0 = 0) :
    dyadicHits T r a f ↔ ∃ k, a < partialSum k (dyadicIncrements T r f) := by
  have hTel (k : ℕ) : partialSum k (dyadicIncrements T r f) =
      f (dyadicT T r (min (k+1) (2^r))) := by
    change partialSum k (fun (i : Fin (2^r)) ↦ (f ∘ dyadicT T r) ((i:ℕ)+1) - (f ∘ dyadicT T r) i) = _
    rw [partialSum_pathDifferences]
    simp [dyadicT_zero,hf]
  simp only [hTel,dyadicHits]
  constructor
  · rintro ⟨k,hk,kHit⟩
    cases k with
    | zero => simp [dyadicT_zero,hf,not_lt_of_ge ha] at kHit
    | succ j => exact ⟨j,by simpa only [min_eq_left hk] using kHit⟩
  · rintro ⟨k,hk⟩
    exact ⟨_, min_le_right ..,hk⟩

theorem dyadicHits_iff_exists {T : ℝ≥0} (hT : 0 < T) (a : ℝ)
    (f : ℝ≥0 → ℝ) (hf : Continuous f) :
    (∃ r, dyadicHits T r a f) ↔ ∃ s ≤ T, a < f s := by
  constructor
  · rintro ⟨r,k,hk,h⟩
    refine ⟨dyadicT T r k,?_,h⟩
    simpa only [dyadicT_last] using dyadicT_mono T r hk
  · rintro ⟨s,hs,h⟩
    have hov := ((hf.continuousAt (x:=s)).tendsto.comp (dyadicBelow_tendsto hT)).eventually_const_lt h
    obtain ⟨r,hr⟩ := hov.exists
    exact ⟨r,_,dyadicBelowIndex_le hT hs r,hr⟩

theorem dyadicOvershoot_tendsto {T : ℝ≥0} (a : ℝ) (ha : 0 ≤ a)
    (f : ℝ≥0 → ℝ) (hf0 : f 0 = 0) (hf : Continuous f)
    (hHit : ∃ r, dyadicHits T r a f) :
    Tendsto (fun r ↦ firstCrossValue a (dyadicIncrements T r f)) atTop (𝓝 a) := by
  classical
  let hP (r : ℕ) := ∃ k, a < partialSum k (dyadicIncrements T r f)
  let k (r : ℕ) : ℕ := if h : hP r then Nat.find h else 0
  have hTel (r j : ℕ) : partialSum j (dyadicIncrements T r f) =
      f (dyadicT T r (min (j+1) (2^r))) := by
    change partialSum j (fun (i : Fin (2^r)) ↦ (f ∘ dyadicT T r) ((i:ℕ)+1) - (f ∘ dyadicT T r) i) = _
    rw [partialSum_pathDifferences]
    simp [dyadicT_zero,hf0]
  have hData (r : ℕ) (hh : hP r) :
      k r < 2^r ∧ f (dyadicT T r (k r)) ≤ a ∧ a < f (dyadicT T r (k r+1)) ∧
        firstCrossValue a (dyadicIncrements T r f) = f (dyadicT T r (k r+1)) := by
    have hK : k r = Nat.find hh := by simp [k,hh]
    have hUp : a < partialSum (k r) (dyadicIncrements T r f) := hK ▸ Nat.find_spec hh
    have hLo (j : ℕ) (hj : j < k r) : partialSum j (dyadicIncrements T r f) ≤ a := by
      apply le_of_not_gt (Nat.find_min hh _)
      rwa [← hK]
    have hN : 0 < (2^r : ℕ) := by positivity
    have hk : k r < 2^r := by
      by_contra! hbad
      have hL := hLo (2^r-1) (by omega)
      rw [hTel,show 2^r-1+1 = (2^r:ℕ) by omega,min_self] at hL
      rw [hTel,min_eq_right (by omega : 2^r ≤ k r+1)] at hUp
      exact (not_lt_of_ge hL) hUp
    refine ⟨hk,?_,?_,?_⟩
    · cases hkr : k r with
      | zero => simpa [dyadicT_zero,hf0] using ha
      | succ j =>
        have hj := hLo j (by omega)
        rw [hTel,min_eq_left (by omega : j+1 ≤ 2^r)] at hj
        exact hj
    · rwa [hTel,min_eq_left (by omega : k r+1 ≤ 2^r)] at hUp
    · rw [firstCrossValue_eq (k:=k r) ⟨hUp,hLo⟩,hTel,min_eq_left (by omega : k r+1 ≤ 2^r)]
  obtain ⟨r₀,hr₀⟩ := hHit
  have hEv : ∀ᶠ r in atTop, hP r :=
    (eventually_ge_atTop r₀).mono (fun r hr ↦
      (dyadicHits_iff_prefix T r a ha f hf0).mp (dyadicHits_mono T a f hr hr₀))
  let b r := dyadicT T r (k r)
  let c r := dyadicT T r (k r+1)
  have hBr : ∀ᶠ r in atTop, b r ∈ Icc 0 T ∧ c r ∈ Icc 0 T ∧ f (b r) ≤ a ∧ a < f (c r) := by
    filter_upwards [hEv] with r hr
    obtain ⟨hk,h₁,h₂,_⟩ := hData r hr
    refine ⟨⟨zero_le,?_⟩,⟨zero_le,?_⟩,h₁,h₂⟩
    · simpa only [dyadicT_last] using dyadicT_mono T r hk.le
    · simpa only [dyadicT_last] using dyadicT_mono T r (by omega : k r+1 ≤ 2^r)
  have hDist (r : ℕ) : dist (c r) (b r) = (T:ℝ)/(2:ℝ)^r := by
    change dist (c r : ℝ) (b r : ℝ) = _
    rw [Real.dist_eq,abs_of_nonneg,dyadicT_succ_sub]
    exact sub_nonneg.mpr (dyadicT_mono T r (Nat.le_succ _))
  have hDist' : Tendsto (fun r ↦ dist (c r) (b r)) atTop (𝓝 0) := by
    simpa only [hDist] using dyadic_step_tendsto T
  have hLim := crossing_overshoot_tendsto isCompact_Icc f hf.continuousOn a b c hBr hDist'
  apply hLim.congr'
  exact hEv.mono (fun r hr ↦ (hData r hr).2.2.2.symm)
end CubeBrownian
#print axioms CubeBrownian.dyadicOvershoot_tendsto
