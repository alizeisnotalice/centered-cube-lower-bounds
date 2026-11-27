import ActualSqrtFiniteMain

open Filter
open scoped ENNReal
namespace CenteredCube
open CenteredCubeSqrt CubeBrownian

theorem sqrt_manuscript_main : SqrtManuscriptMain := by
  apply exact_main_from_actual_finite_grid
  intro p hp hp1 η hη
  have hL := actualSmoothedGridMean_unconditional_lower (η/2) (by positivity)
  filter_upwards [hL] with T hT b hb hbc
  obtain ⟨w,hw,hG⟩ := hT.2.exists
  exact paper_actual_finite_eventual_coefficient hp hp1 hη hb T w hT.1 hw
    (by simpa [paperScaleWindow] using hG) hbc

theorem sqrt_manuscript_rational : SqrtManuscriptRational :=
  sqrt_manuscript_rational_of_main sqrt_manuscript_main

#print axioms sqrt_manuscript_main
#print axioms sqrt_manuscript_rational
end CenteredCube
