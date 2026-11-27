import Std

namespace CenteredCubeLowerBounds

/-- The rounding rule in the Rudin–Shapiro manuscript, over the rationals. -/
theorem frequency_rounding (A : Rat) :
    (-2 < 4 * ((A / 4 + 1 / 2).floor : Rat) - A) ∧
      4 * ((A / 4 + 1 / 2).floor : Rat) - A ≤ 2 := by
  have lower := Rat.floor_le (A / 4 + 1 / 2)
  have upper := Rat.lt_floor_add_one (A / 4 + 1 / 2)
  grind

/-- The rational margin in the proof of the simplified square-root constant. -/
theorem pi_bound_margin :
    (68 / 5 : Rat)^2 - 58 * (22 / 7) = 468 / 175 := by
  grind

/-- The last rational comparison in the proof of the simplified constant. -/
theorem square_root_constant_comparison : (1 / 35 : Rat) < 87 / 2992 := by
  grind

/-- The same arithmetic comparison with the two squared numerators expanded. -/
theorem square_root_constant_squared :
    (220 : Nat)^2 * 58 * 22 < (35 * 87 : Nat)^2 * 7 := by
  decide

end CenteredCubeLowerBounds

#print axioms CenteredCubeLowerBounds.frequency_rounding
#print axioms CenteredCubeLowerBounds.pi_bound_margin
#print axioms CenteredCubeLowerBounds.square_root_constant_comparison
#print axioms CenteredCubeLowerBounds.square_root_constant_squared
