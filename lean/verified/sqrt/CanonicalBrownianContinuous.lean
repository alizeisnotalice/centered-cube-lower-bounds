import BrownianContinuousModification
import BrownianDyadicProbability
import CanonicalPreBrownian

namespace CubeBrownian
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

theorem preBrownian_has_dyadic_continuous_modification {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) :
    IsBrownianReal (brownianDyadicModification B) P := by
  apply brownian_dyadic_modification P B hB
  · apply preBrownian_ae_dyadic_grid hB dyadicClock
    intro m k
    change dist (dyadicClock m (k+1)) (dyadicClock m k) ≤ (1/2:ℝ)^m
    rw [one_div_pow,dyadicClock_adjacent_dist]
  · intro t
    apply preBrownian_ae_dyadic_approx hB t
    intro m
    change dist (dyadicClock m (dyadicIndex m t)) t ≤ (1/2:ℝ)^m
    rw [one_div_pow]
    exact dyadic_round_dist_le m t

noncomputable def paperWienerBrownian (t : ℝ≥0) (ω : ℝ≥0 → ℝ) : ℝ :=
  brownianDyadicModification (fun s f => f s) t ω

theorem paperWienerBrownian_isBrownian :
    IsBrownianReal paperWienerBrownian paperWienerCylinder :=
  preBrownian_has_dyadic_continuous_modification paperWienerCylinder_isPreBrownian

#print axioms preBrownian_has_dyadic_continuous_modification
#print axioms paperWienerBrownian_isBrownian
end CubeBrownian
