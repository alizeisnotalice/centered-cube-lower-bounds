import SqrtJointTrace
import SqrtLabelSpace

namespace CenteredCubeSqrt

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- Ratio defects on the actual field subspace, before taking a logarithm
in the cyclic multiplicative group. -/
noncomputable def labelRatioSet {b d : ℕ} (t : Fin b → LabelField d) : Set (LabelField d) :=
  {g | ∃ a ∈ labelSpace t, ∃ c ∈ labelSpace t, a ≠ 0 ∧ c ≠ 0 ∧ a ≠ c ∧ a/c=g}

theorem overlap_mem_iff_actual {b d : ℕ} {t : Fin b → LabelField d}
    {g : (LabelField d)ˣ} {x : LabelField d} :
    x ∈ traceOverlap t g ↔ x ∈ labelSpace t ∧
      ∃ y ∈ labelSpace t, (g:LabelField d)*y=x := by
  have e : Submodule.span (ZMod 2) (Set.range (fun i => (g:LabelField d)*t i)) =
    (labelSpace t).map (LinearMap.mulLeft (ZMod 2) (g:LabelField d)) := by
    rw [labelSpace, Submodule.map_span, ← Set.range_comp]
    rfl
  rw [traceOverlap, Submodule.mem_inf, e]
  rfl

theorem overlap_nonzero_iff_defect {b d : ℕ} {t : Fin b → LabelField d}
    {g : (LabelField d)ˣ} (hg : (g:LabelField d) ≠ 1) :
    (∃ x ∈ traceOverlap t g, x ≠ 0) ↔ (g:LabelField d) ∈ labelRatioSet t := by
  constructor
  · rintro ⟨x,hx,hx0⟩
    obtain ⟨hxW,y,hyW,he⟩ := overlap_mem_iff_actual.mp hx
    have hy0 : y ≠ 0 := by
      intro hy
      rw [hy,mul_zero] at he
      exact hx0 he.symm
    have hxy : x ≠ y := by
      intro h
      apply hg
      apply mul_right_cancel₀ hy0
      rw [he,h,one_mul]
    exact ⟨x,hxW,y,hyW,hx0,hy0,hxy,(div_eq_iff hy0).mpr he.symm⟩
  · rintro ⟨x,hx,y,hy,hx0,hy0,_,hf⟩
    exact ⟨x,overlap_mem_iff_actual.mpr ⟨hx,y,hy,((div_eq_iff hy0).mp hf).symm⟩,hx0⟩

theorem traceOverlap_regular_bot {b d : ℕ} {t : Fin b → LabelField d}
    {g : (LabelField d)ˣ} (hg : (g:LabelField d) ≠ 1)
    (h : (g:LabelField d) ∉ labelRatioSet t) : traceOverlap t g = ⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  have e : x=0 := by
    by_contra hx0
    exact h ((overlap_nonzero_iff_defect hg).mp ⟨x,hx,hx0⟩)
  rw [e]
  exact Submodule.zero_mem _

theorem defect_overlap_rank_one {b d : ℕ} {t : Fin b → LabelField d}
    {g : (LabelField d)ˣ}
    (hW : MultiplicativeSidon {x : LabelField d | x ∈ labelSpace t ∧ x ≠ 0})
    (hg : (g:LabelField d) ≠ 1) (hd : (g:LabelField d) ∈ labelRatioSet t) :
    Module.finrank (ZMod 2) (traceOverlap t g) = 1 := by
  obtain ⟨x,hx,hx0⟩ := (overlap_nonzero_iff_defect hg).mpr hd
  have onlyX (z : LabelField d) (hz : z ∈ traceOverlap t g) (hz0 : z ≠ 0) : z=x := by
    obtain ⟨hxW,a,ha,ea⟩ := overlap_mem_iff_actual.mp hx
    obtain ⟨hzW,c,hc,ec⟩ := overlap_mem_iff_actual.mp hz
    have a0 : a ≠ 0 := fun h => hx0 (by rw [← ea,h,mul_zero])
    have c0 : c ≠ 0 := fun h => hz0 (by rw [← ec,h,mul_zero])
    exact (translate_intersection_nonzero_unique hW hg ⟨hzW,hz0⟩ ⟨hc,c0⟩
      ⟨hxW,hx0⟩ ⟨ha,a0⟩ c0 a0 ec.symm ea.symm).1
  have e : traceOverlap t g = Submodule.span (ZMod 2) {x} := by
    apply le_antisymm
    · intro z hz
      by_cases h : z=0
      · rw [h]
        exact Submodule.zero_mem _
      · rw [onlyX z hz h]
        exact Submodule.subset_span (by simp)
    · rw [Submodule.span_le]
      simpa using hx
  rw [e,finrank_span_singleton hx0]

#print axioms overlap_nonzero_iff_defect
#print axioms traceOverlap_regular_bot
#print axioms defect_overlap_rank_one

end CenteredCubeSqrt
