import SqrtLowerLiminf

open Filter
open scoped ENNReal
namespace CenteredCube

/-- Manuscript Theorem 1. Enumerating positive dimensions explicitly by n+1
does not exclude any dimension or use a subsequence. -/
def SqrtManuscriptMain : Prop :=
  ENNReal.ofReal (87 / (220 * Real.sqrt (58 * Real.pi))) ≤
    liminf (fun m : ℕ => weakConstant (m+1) /
      ENNReal.ofReal (Real.sqrt ((m+1:ℕ):ℝ))) atTop

/-- Manuscript's subsequent rational-bound theorem, not the main theorem. -/
def SqrtManuscriptRational : Prop :=
  ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
    ENNReal.ofReal (Real.sqrt (n:ℝ)/35) ≤ weakConstant n

theorem sqrt_manuscript_scope_iff :
    SqrtManuscriptMain ↔
      ENNReal.ofReal CubeSqrtEnd.paperConstant ≤ liminf sqrtNormalizedWeakConstant atTop := by
  unfold SqrtManuscriptMain CubeSqrtEnd.paperConstant
  rw [← liminf_nat_add sqrtNormalizedWeakConstant 1]
  rfl

theorem sqrt_manuscript_rational_of_main (h : SqrtManuscriptMain) :
    SqrtManuscriptRational := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp
    (eventually_one_thirty_fifth_of_exact_liminf (sqrt_manuscript_scope_iff.mp h))
  exact ⟨N,fun n hn => (hN n hn).le⟩

#print axioms sqrt_manuscript_scope_iff
#print axioms sqrt_manuscript_rational_of_main
end CenteredCube
