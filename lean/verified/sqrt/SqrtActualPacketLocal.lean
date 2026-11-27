import SqrtActualLocalBaselineLimit
import SqrtAllIntegerPackets

namespace CenteredCubeSqrt
open Set Filter MeasureTheory CubeSqrtOverlap
open scoped Topology BigOperators
set_option maxHeartbeats 1300000
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem actual_v_exact_scale (p : ℝ) {n d : ℕ} (hd : 0<d) :
    (n:ℝ)*p^2=(29/9)*(paperPeriod d:ℝ)^2*paperV p n d := by
  have h : (paperPeriod d:ℝ)≠0 := by
    exact_mod_cast (show paperPeriod d≠0 by have := paperPeriod_one_le hd; omega)
  unfold paperV
  field_simp

theorem paper_packet_localLength_eq (K v P A : ℝ) (i a : ℕ) :
    localLength (paperPacketLength K v P A i 0) (K*v) ((a:ℝ)*A) =
      paperPacketLength K v P A i a := by
  unfold localLength paperPacketLength
  simp only [Nat.cast_zero,zero_mul,add_zero]
  ring

theorem actualPacketChoice_local_source {w p v P A : ℝ} {b d N : ℕ} {R : Finset ℕ}
    (h : ActualPacketChoice w v P A b d N R) :
    ∃ X : ℝ→ℝ→ℝ, ∀ i∈R,
      let K := (paperPeriod d:ℝ)
      let L0 := paperPacketLength K v P A i 0
      ActualSafeLocalSource w p v b d L0 X ∧ L0∈paperScaleWindow ∧
      ∀ a : Fin (N+1), localLength L0 (K*v) ((a:ℝ)*A)∈paperScaleWindow := by
  obtain ⟨mesh,_,_,hd,hK,g,hg,t,ht,hshort,_,hL,_⟩ := h
  let _ : NeZero (2^d-1) := hK
  let K := (paperPeriod d:ℝ)
  let X := actualWindowPerturbation (ordinalPhaseLabel hd g hg t) (paperMeshM v) p (paperMeshDelta w K v)
  refine ⟨X,?_⟩
  intro i hi
  have at_zero := hL i hi 0
  refine ⟨⟨mesh,hd,hK,g,hg,t,ht,hshort,at_zero.2,rfl⟩,at_zero.1,?_⟩
  intro a
  rw [paper_packet_localLength_eq]
  exact (hL i hi a).1

theorem actualPacketChoice_local_source_eventually {l : Filter ℕ} {w p P A : ℝ}
    {b d : ℕ→ℕ} {v : ℕ→ℝ} {N : ℕ} {R : ℕ→Finset ℕ}
    (h : ∀ᶠ n in l, ActualPacketChoice w (v n) P A (b n) (d n) N (R n)) :
    ∃ X : ℕ→ℝ→ℝ→ℝ, ∀ᶠ n in l, ∀ i∈R n,
      let K := (paperPeriod (d n):ℝ)
      let L0 := paperPacketLength K (v n) P A i 0
      ActualSafeLocalSource w p (v n) (b n) (d n) L0 (X n) ∧ L0∈paperScaleWindow ∧
      ∀ a : Fin (N+1), localLength L0 (K*v n) ((a:ℝ)*A)∈paperScaleWindow := by
  classical
  let W (n : ℕ) (X : ℝ→ℝ→ℝ) : Prop := ∀ i∈R n,
      let K := (paperPeriod (d n):ℝ)
      let L0 := paperPacketLength K (v n) P A i 0
      ActualSafeLocalSource w p (v n) (b n) (d n) L0 X ∧ L0∈paperScaleWindow ∧
      ∀ a : Fin (N+1), localLength L0 (K*v n) ((a:ℝ)*A)∈paperScaleWindow
  let X (n : ℕ) := if h : ∃ X, W n X then h.choose else fun _ _ => 0
  refine ⟨X,?_⟩
  filter_upwards [h] with n hn
  have H : ∃ X, W n X := actualPacketChoice_local_source (p:=p) hn
  dsimp only [X]
  rw [dite_eq_left H]
  exact H.choose_spec

#print axioms actual_v_exact_scale
#print axioms actualPacketChoice_local_source_eventually
end CenteredCubeSqrt
