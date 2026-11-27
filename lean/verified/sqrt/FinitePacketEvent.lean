import FiniteWinner

open Set
namespace CubeSqrtProbability

theorem finite_packet_exceedance_eq_iUnion {Ω I : Type*} [Finite I] [Nonempty I]
    (s : I → Ω → ℝ) (h : ℝ) :
    {w | h < ⨆ i, s i w} = ⋃ i, {w | h < s i w} := by
  ext w
  simp only [mem_ofPred_eq,mem_iUnion]
  constructor
  · intro hw
    obtain ⟨i,hi⟩ := exists_eq_ciSup_of_finite (f := fun i : I ↦ s i w)
    exact ⟨i,hi.symm ▸ hw⟩
  · rintro ⟨i,hi⟩
    exact hi.trans_le (le_ciSup (finite_range (fun i : I ↦ s i w)).bddAbove i)

end CubeSqrtProbability
#print axioms CubeSqrtProbability.finite_packet_exceedance_eq_iUnion
