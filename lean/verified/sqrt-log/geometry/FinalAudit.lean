import PaperSqrtLog

open scoped ENNReal

theorem centered_cube_lower_bound_sqrt_div_log_clean :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ENNReal.ofReal (c * Real.sqrt (n : ℝ) / Real.log (n : ℝ)) ≤
        CenteredCube.weakConstant n :=
  CenteredCube.RudinDensity.sqrtLogLowerBound_paper

#print axioms centered_cube_lower_bound_sqrt_div_log_clean
