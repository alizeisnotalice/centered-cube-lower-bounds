import SqrtPaperKernelChoice
import PaperPacketGeometry
import PaperPacketCountRates
import RetainedFirstSum

namespace CenteredCubeSqrt
open Set Filter Finset CubeSqrtOverlap MvPolynomial
open scoped Topology BigOperators
set_option maxHeartbeats 1700000
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem integer_periodic_defect_lift {K : ℕ} [NeZero K] (k : ℤ) :
    ∃ j : ℤ, (k:ℝ)=(((k:ZMod K).val:ℕ):ℝ)+(j:ℝ)*(K:ℝ) := by
  let a := (k:ZMod K).val
  have h0 : ((k-(a:ℤ):ℤ):ZMod K)=0 := by
    rw [Int.cast_sub, Int.cast_natCast,show (a:ZMod K)=(k:ZMod K) by
      dsimp [a]; exact ZMod.natCast_zmod_val _,sub_self]
  obtain ⟨m,hm⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h0
  have H : (k:ℝ)-(a:ℝ)=(K:ℝ)*(m:ℝ) := by exact_mod_cast hm
  exact ⟨m,by linarith [mul_comm (K:ℝ) (m:ℝ)]⟩

noncomputable def actualRetainedPackets {b d : ℕ} [NeZero (2^d-1)]
    (hd : 0<d) (g : (LabelField d)ˣ) (hg : orderOf g=2^d-1) (t : Fin b→LabelField d)
    (v P A : ℝ) (N : ℕ) : Finset ℕ := by
  classical
  let K := (paperPeriod d:ℝ)
  exact (Finset.range (rawPacketCount (K*v/18) ((N:ℝ)*A) P)).filter fun i =>
    ∀ a : Fin (N+1), actualSafeLifts hd g hg t (paperPacketLength K v P A i a)

theorem actual_retained_packets_mem {b d : ℕ} [NeZero (2^d-1)]
    (hd : 0<d) (g : (LabelField d)ˣ) (hg : orderOf g=2^d-1) (t : Fin b→LabelField d)
    (v P A : ℝ) (N i : ℕ) :
    let K := (paperPeriod d:ℝ)
    i∈actualRetainedPackets hd g hg t v P A N ↔
      i∈Finset.range (rawPacketCount (K*v/18) ((N:ℝ)*A) P) ∧
      ∀ a : Fin (N+1), actualSafeLifts hd g hg t (paperPacketLength K v P A i a) := by
  classical
  unfold actualRetainedPackets
  exact Finset.mem_filter

theorem actual_retained_packets_deletion_bound {b d : ℕ} [NeZero (2^d-1)]
    (hd : 0<d) (g : (LabelField d)ˣ) (hg : orderOf g=2^d-1) (t : Fin b→LabelField d)
    (h0 : ∀ a, labelValue t a ≠0)
    (hp : Function.Injective (fun z : Sym2 (NonzeroBinary b) => eval t (symLabelProduct z)))
    {v P A : ℝ} (hv : 0<v) (hP : 0<P) (hA : 0≤A) (N : ℕ)
    (hK : 18≤paperPeriod d) (hV : (N:ℝ)*A≤(paperPeriod d:ℝ)*v/18)
    (hB : (2:ℝ)^b<2*v) :
    let K := (paperPeriod d:ℝ)
    let deleted := Finset.range (rawPacketCount (K*v/18) ((N:ℝ)*A) P) \
      actualRetainedPackets hd g hg t v P A N
    (deleted.card:ℝ)≤((N:ℝ)+1)*(4*v^2)*(2*v/P+1) := by
  classical
  let K := (paperPeriod d:ℝ)
  let B := (2:ℝ)^b
  let S := Finset.range (rawPacketCount (K*v/18) ((N:ℝ)*A) P)
  let deleted := S \ actualRetainedPackets hd g hg t v P A N
  let F := (cyclicDefects hd g hg t)
  let _ : Fintype F := Fintype.ofFinite F
  let D (j : F) : ℝ := ((j.1.val:ℕ):ℝ)
  have hc : Fintype.card F=(2^b-1)*(2^b-2) := by
    rw [←Nat.card_eq_fintype_card]
    exact cyclicDefects_card hd g hg h0 hp
  have hc' : (Fintype.card F:ℝ)≤4*v^2 := by
    have L : Fintype.card F ≤ ((2:ℕ)^b)^2 := by
      rw [hc,sq]
      exact Nat.mul_le_mul (Nat.sub_le ..) (Nat.sub_le ..)
    have H : (Fintype.card F:ℝ)≤B^2 := by dsimp [B]; exact_mod_cast L
    exact H.trans (by nlinarith [pow_le_pow_left₀ (show 0≤B by positivity) hB.le 2])
  have HK : 5≤K := by
    have h : 18≤K := by dsimp [K]; exact_mod_cast hK
    linarith
  have hbad (i : ℕ) (hi : i∈deleted) : ∃ (a : Fin (N+1)) (j : F) (m : ℤ),
      |K*(paperPacketLength K v P A i a.1-1)-(D j+(m:ℝ)*K)|≤2 := by
    obtain ⟨hr,hn⟩ := Finset.mem_sdiff.mp hi
    have H : ¬∀ a : Fin (N+1), actualSafeLifts hd g hg t (paperPacketLength K v P A i a) := by
      intro hh
      exact hn ((actual_retained_packets_mem hd g hg t v P A N i).2 ⟨hr,hh⟩)
    obtain ⟨a,h⟩ := not_forall.mp H
    simp only [actualSafeLifts,not_forall,not_lt] at h
    obtain ⟨k,hF,hk⟩ := h
    obtain ⟨m,hm⟩ := integer_periodic_defect_lift (K:=2^d-1) k
    let j : F := ⟨(k:ZMod (2^d-1)),hF⟩
    refine ⟨a,j,m,?_⟩
    change (k:ℝ)=D j+(m:ℝ)*K at hm
    rw [←hm,abs_sub_comm]
    exact hk
  have H := paper_unsafe_packet_deletion_budget D K v P A HK hv hP hA N hV deleted
    (fun _ hh => (Finset.mem_sdiff.mp hh).1) hbad
  exact H.trans (by
    have hh : 0≤2*v/P+1 := by positivity
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc' (by positivity)) hh)

#print axioms integer_periodic_defect_lift
#print axioms actual_retained_packets_deletion_bound
end CenteredCubeSqrt
