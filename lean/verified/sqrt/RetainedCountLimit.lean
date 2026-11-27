import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Topology.Instances.Real.Lemmas
import RetainedCount
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

open Finset Filter
open scoped Topology
namespace CubeSqrtOverlap

noncomputable def rawPacketCount (V T P : ℝ) : ℕ :=
  ⌊(V-T)/P⌋₊+1

theorem raw_packet_ratio_limit (V : ℕ → ℝ) (T P : ℝ)
    (hV : Tendsto V atTop atTop) (hP : 0 < P) (hT : 0 ≤ T) :
    Tendsto (fun n ↦ ((rawPacketCount (V n) T P):ℝ)/V n) atTop (𝓝 (1/P)) := by
  apply Metric.tendsto_nhds.2
  intro ε hε
  have hUb := (hV.const_div_atTop (T/P+1)).eventually_lt_const hε
  filter_upwards [hV.eventually_ge_atTop T,hV.eventually_gt_atTop 0,hUb] with n hNT hn0 hεn
  rw [Real.dist_eq]
  have he : ((rawPacketCount (V n) T P):ℝ)/V n-1/P =
      (((rawPacketCount (V n) T P):ℝ)-V n/P)/V n := by
    field_simp [hn0.ne', hP.ne'] <;> ring
  rw [he,abs_div,abs_of_pos hn0]
  exact (div_le_div_of_nonneg_right (raw_packet_count_error (V n) T P hP hT hNT) hn0.le).trans_lt hεn

/-- Deterministic retained original-index count asymptotic: an o(V)
deletion budget leaves the exact same leading packet-grid density. -/
theorem retained_packet_ratio_limit (V : ℕ → ℝ) (T P : ℝ)
    (hV : Tendsto V atTop atTop) (hP : 0 < P) (hT : 0 ≤ T)
    (R : ℕ → Finset ℕ)
    (hR : ∀ᶠ n in atTop, R n ⊆ range (rawPacketCount (V n) T P))
    (hDel : Tendsto (fun n ↦ (((range (rawPacketCount (V n) T P) \ R n).card):ℝ)/V n)
        atTop (𝓝 0)) :
    Tendsto (fun n ↦ ((R n).card:ℝ)/V n) atTop (𝓝 (1/P)) := by
  have H := (raw_packet_ratio_limit V T P hV hP hT).sub hDel
  rw [sub_zero] at H
  apply H.congr'
  filter_upwards [hR] with n hn
  change ((rawPacketCount (V n) T P):ℝ)/V n -
    (((range (rawPacketCount (V n) T P) \ R n).card):ℝ)/V n = ((R n).card:ℝ)/V n
  have h := card_sdiff_add_card_eq_card hn
  rw [card_range] at h
  have hh : (((range (rawPacketCount (V n) T P) \ R n).card):ℝ)+((R n).card:ℝ) =
      ((rawPacketCount (V n) T P):ℝ) := by exact_mod_cast h
  rw [←sub_div,←hh,add_sub_cancel_left]

/-- The overlap argument also needs the retained set eventually nonempty,
which follows from the positive limiting density and diverging raw scale. -/
theorem retained_eventually_nonempty
    (V : ℕ → ℝ) (P : ℝ) (hP : 0 < P) (hV : Tendsto V atTop atTop)
    (R : ℕ → Finset ℕ) (hRatio : Tendsto (fun n ↦ ((R n).card:ℝ)/V n) atTop (𝓝 (1/P))) :
    ∀ᶠ n in atTop, (R n).Nonempty := by
  filter_upwards [hRatio.eventually_const_lt (show 0 < 1/P by positivity),hV.eventually_gt_atTop 0]
    with n hn hv
  apply Finset.card_pos.mp
  have hh : 0 < ((R n).card:ℝ) := by
    by_contra! h
    exact (not_le_of_gt hn) (div_nonpos_of_nonpos_of_nonneg h hv.le)
  exact_mod_cast hh

end CubeSqrtOverlap
#print axioms CubeSqrtOverlap.retained_packet_ratio_limit
#print axioms CubeSqrtOverlap.retained_eventually_nonempty
