import SqrtExactMain

open Filter
open scoped ENNReal

theorem replayed_original_sqrt_liminf :
    ENNReal.ofReal (87 / (220 * Real.sqrt (58 * Real.pi))) ≤
      liminf
        (fun m : ℕ => CenteredCube.weakConstant (m + 1) /
          ENNReal.ofReal (Real.sqrt ((m + 1 : ℕ) : ℝ)))
        atTop :=
  CenteredCube.sqrt_manuscript_main

theorem replayed_original_rational_sqrt :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ENNReal.ofReal (Real.sqrt (n : ℝ) / 35) ≤ CenteredCube.weakConstant n :=
  CenteredCube.sqrt_manuscript_rational

#print axioms replayed_original_sqrt_liminf
#print axioms replayed_original_rational_sqrt
