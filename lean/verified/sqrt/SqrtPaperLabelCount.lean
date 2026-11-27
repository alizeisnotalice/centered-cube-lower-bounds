import SqrtActualCyclicFibers
import SqrtDefectHyperplane
import Mathlib.SetTheory.Cardinal.NatCard

namespace CenteredCubeSqrt

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
open Classical

theorem two_power_div_of_le {a d : ℕ} (h : a ≤ d) :
    2^d / 2^a = 2^(d-a) := by
  have e : (2:ℕ)^a * 2^(d-a) = 2^d := by rw [← pow_add, Nat.add_sub_of_le h]
  rw [← e, Nat.mul_div_cancel_left _ (by positivity)]

/-- The manuscript's regular cyclic count (q/B^2-1_{{y=0}}) with literal
trace labels and the actual primitive period. -/
theorem manuscript_regular_cyclic_label_count {b d : ℕ} (hd : 0 < d)
    (g : (LabelField d)ˣ) (hg : orderOf g = 2^d-1) {t : Fin b → LabelField d}
    (ht : LinearIndependent (ZMod 2) t) (k : ZMod (2^d-1))
    (hk : (phaseState hd g hg k : LabelField d) ≠ 1)
    (hk' : (phaseState hd g hg k : LabelField d) ∉ labelRatioSet t)
    (hdim : 2*b ≤ d) (y : LabelOutput b) :
    Nat.card {j : ZMod (2^d-1) //
      Sum.elim (phaseLabel hd g hg t j) (phaseLabel hd g hg t (j+k)) = y} =
      2^d/(2^b)^2 - if y=0 then 1 else 0 := by
  rw [phaseLabel_fiber_count,
    jointTrace_regular_fiber hd ht _ (traceOverlap_regular_bot hk hk')]
  have hdiv : (2:ℕ)^d/(2^b)^2 = 2^(d-2*b) := by
    rw [← pow_mul, Nat.mul_comm b 2, two_power_div_of_le hdim]
  rw [hdiv]

/-- On the actual deficient hyperplane the count doubles; outside it
there are no states. The zero correction is made only after restricting
the full field to the primitive orbit. -/
theorem manuscript_defective_cyclic_label_count {b d : ℕ} (hd : 0 < d)
    (g : (LabelField d)ˣ) (hg : orderOf g = 2^d-1) {t : Fin b → LabelField d}
    (ht : LinearIndependent (ZMod 2) t) (k : ZMod (2^d-1))
    (hk : (phaseState hd g hg k : LabelField d) ≠ 1)
    (hk' : (phaseState hd g hg k : LabelField d) ∈ labelRatioSet t)
    (hS : MultiplicativeSidon {x : LabelField d | x ∈ labelSpace t ∧ x ≠ 0})
    (a c : NonzeroBinary b)
    (hmatch : labelValue t a = (phaseState hd g hg k : LabelField d)*labelValue t c)
    (y : LabelOutput b) :
    Nat.card {j : ZMod (2^d-1) //
      Sum.elim (phaseLabel hd g hg t j) (phaseLabel hd g hg t (j+k)) = y} =
      if traceMatchForm a c y = 0 then
        2^(d-(2*b-1)) - (if y=0 then 1 else 0) else 0 := by
  rw [phaseLabel_fiber_count]
  have hr := defect_overlap_rank_one hS hk hk'
  have hR := traceDefect_image_hyperplane ht _ a c hmatch hr
  by_cases hy : traceMatchForm a c y = 0
  · rw [ite_eq_left hy]
    have h : y ∈ (jointTrace t (phaseState hd g hg k)).range := by
      rw [hR]
      exact LinearMap.mem_ker.mpr hy
    rw [jointTrace_nonzero_fiber hd ht _ h, hr]
  · rw [ite_eq_right hy]
    apply (Finite.card_eq_zero_iff).mpr
    refine ⟨fun ⟨x,hx,_⟩ => hy ?_⟩
    have hm : y ∈ (jointTrace t (phaseState hd g hg k)).range := ⟨x,hx⟩
    rw [hR] at hm
    exact LinearMap.mem_ker.mp hm

theorem actual_defect_matching_labels {b d : ℕ} {t : Fin b → LabelField d}
    {u : (LabelField d)ˣ} (h : (u:LabelField d) ∈ labelRatioSet t) :
    ∃ a c : NonzeroBinary b, a ≠ c ∧ labelValue t a = (u:LabelField d)*labelValue t c := by
  obtain ⟨x,hx,z,hz,x0,z0,hxz,hr⟩ := h
  obtain ⟨a,ha⟩ := labelSpace_nonzero_is_labelValue t hx x0
  obtain ⟨c,hc⟩ := labelSpace_nonzero_is_labelValue t hz z0
  refine ⟨a,c,?_,?_⟩
  · intro e
    apply hxz
    rw [← ha,← hc,e]
  · rw [ha,hc]
    exact (div_eq_iff z0).mp hr

/-- At zero shift the output is diagonal, and the diagonal fiber is q/B,
excluding the zero field state only at the zero output. -/
theorem manuscript_zero_cyclic_label_count {b d : ℕ} (hd : 0 < d)
    (g : (LabelField d)ˣ) (hg : orderOf g = 2^d-1) {t : Fin b → LabelField d}
    (ht : LinearIndependent (ZMod 2) t) (hbd : b ≤ d) (y : LabelOutput b) :
    Nat.card {j : ZMod (2^d-1) //
      Sum.elim (phaseLabel hd g hg t j) (phaseLabel hd g hg t (j+0)) = y} =
      if (fun i => y (.inl i)) = (fun i => y (.inr i)) then
        2^d/2^b - (if y=0 then 1 else 0) else 0 := by
  rw [phaseLabel_fiber_count]
  have e0 : phaseState hd g hg 0 = 1 := map_one (cyclicStateEquiv hd g hg)
  rw [e0]
  have ha : Module.finrank (ZMod 2) (traceLabelMap t).range = b := by
    rw [actual_traceLabel_rank, finrank_span_eq_card ht, Fintype.card_fin]
  have hSurj : Function.Surjective (traceLabelMap t) := by
    apply LinearMap.range_eq_top.mp
    exact Submodule.eq_top_of_finrank_eq (by simp [ha])
  have hR (x : LabelField d) : jointTrace t 1 x = Sum.elim (traceLabelMap t x) (traceLabelMap t x) := by
    funext i
    cases i <;> simp [jointTrace,jointTraceRows]
  by_cases he : (fun i => y (.inl i)) = (fun i => y (.inr i))
  · rw [ite_eq_left he]
    have hMem : y ∈ (jointTrace t 1).range := by
      obtain ⟨x,hx⟩ := hSurj (fun i => y (.inl i))
      refine ⟨x,?_⟩
      rw [hR,hx]
      funext i
      cases i with
      | inl i => rfl
      | inr i => exact congrFun he i
    have hRank : Module.finrank (ZMod 2) (jointTrace t 1).range = b := by
      rw [jointTrace_rank ht]
      have hW : Module.finrank (ZMod 2) (traceOverlap t 1) = b := by
        have hm : (fun i => ((1:(LabelField d)ˣ):LabelField d)*t i) = t := by
          funext i
          rw [Units.val_one,one_mul]
        unfold traceOverlap
        rw [hm, inf_idem, finrank_span_eq_card ht, Fintype.card_fin]
      rw [hW]
      omega
    rw [finite_linear_nonzero_fiber, actual_binary_fiber_card _ hMem, hRank,
      GaloisField.finrank 2 hd.ne', two_power_div_of_le hbd]
    by_cases hy : y=0 <;> simp [hy]
  · rw [ite_eq_right he]
    apply (Finite.card_eq_zero_iff).mpr
    refine ⟨fun ⟨x,hx,_⟩ => he ?_⟩
    rw [hR] at hx
    funext i
    exact (congrFun hx (.inl i)).symm.trans (congrFun hx (.inr i))

#print axioms actual_defect_matching_labels
#print axioms manuscript_zero_cyclic_label_count

#print axioms manuscript_regular_cyclic_label_count
#print axioms manuscript_defective_cyclic_label_count

end CenteredCubeSqrt
