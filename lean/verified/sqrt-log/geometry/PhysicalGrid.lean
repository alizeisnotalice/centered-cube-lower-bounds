import BudgetConversion
import ActualGrowth
import TensorAverage

open Filter MeasureTheory Set
open scoped Topology ENNReal

namespace CenteredCube.RudinDensity

theorem paperU_is_centerScale (n : ℕ) : paperU n = centerScale n (paperK n) := rfl

theorem eventually_scale_bounds {a : ℝ} (ha : 0 < a) :
    ∀ᶠ n in atTop, 64 ≤ paperK n ∧ 2*paperU n^2/a^2 ≤ (paperK n:ℝ) ∧
      (2*Real.pi*64+8)/(paperK n:ℝ) ≤ min globalMu globalNu/2 := by
  obtain ⟨J,hJ,H⟩ := exists_global_cutoff
  have ha2 : 0 < a^2/2 := by positivity
  filter_upwards [paperK_tends_top_real.eventually_ge_atTop (J:ℝ),
    paperU_sq_over_K_zero.eventually (gt_mem_nhds ha2), eventually_paperK_pos] with n hKn hQ hk
  have hKn' : J ≤ paperK n := by exact_mod_cast hKn
  have hpos : 0 < (paperK n:ℝ) := by exact_mod_cast hk
  have hQ' := (div_le_iff₀ hpos).1 hQ.le
  have hside : 2*paperU n^2/a^2 ≤ (paperK n:ℝ) := by
    apply (div_le_iff₀ (by positivity : 0<a^2)).2
    nlinarith only [hQ']
  exact ⟨hJ.trans hKn', hside,H _ hKn'⟩

noncomputable def paperHitSet (n : ℕ) (a : ℝ) : Set (Fin n → ℝ) :=
  ⋃ j < paperGridM (paperK n) a, hitPoint n (paperK n) (paperGrid (paperK n) a (paperU n) j)

theorem measurable_paperHitSet (n : ℕ) (a : ℝ) : MeasurableSet (paperHitSet n a) :=
  MeasurableSet.iUnion fun _ => MeasurableSet.iUnion fun _ => measurableSet_hitPoint _ _ _

noncomputable def paperHaloC (a : ℝ) : ℝ := marginalC*Real.exp (-(1/2))/(36000*Real.pi*a)

theorem paperHaloC_pos {a : ℝ} (ha : 0 < a) : 0 < paperHaloC a := by
  unfold paperHaloC
  exact div_pos (mul_pos marginalC_pos (Real.exp_pos _)) (by positivity)

theorem lower_from_grid_mass {n : ℕ} {a : ℝ} (hn : 0 < n) (ha : 0 < a)
    (hk : 0 < paperK n) (hL : 1 ≤ Real.log (n:ℝ))
    (hbound : 2 ≤ (paperK n:ℝ)/(100*a)) (hround : |paperU n^2-Real.log (n:ℝ)| ≤ 1) :
    paperHaloC a / Real.log (n:ℝ) ≤ (paperGridM (paperK n) a:ℝ)*rawMarginal (paperU n)/2 := by
  let u := paperU n
  let L := Real.log (n:ℝ)
  have hu : 0 < u := paperU_pos hn hk
  have hPos : 0 < L := by linarith only [hL]
  have hU2 : u^2 ≤ 2*L := by linarith only [hL,(abs_le.mp hround).2]
  have hM := grid_exp_mass_lower hn ha hk hbound hround
  have first : (marginalC/(2*u))*(Real.exp (-(1/2))/(9000*Real.pi*a*u)) ≤
    (marginalC/(2*u))*((paperGridM (paperK n) a:ℝ)*Real.exp (-(u^2/2))) :=
    mul_le_mul_of_nonneg_left hM (by positivity [marginalC_pos])
  have H : paperHaloC a / L ≤ marginalC*Real.exp (-(1/2))/(18000*Real.pi*a*u^2) := by
    unfold paperHaloC
    rw [div_div]
    apply div_le_div_of_nonneg_left (by positivity [marginalC_pos]) (by positivity)
    have h := mul_le_mul_of_nonneg_left hU2 (show 0 ≤ 18000*Real.pi*a by positivity)
    linarith only [h]
  apply H.trans
  convert first using 1 <;> simp only [rawMarginal, ← show paperU n = u from rfl] <;> ring

theorem paper_hit_cube_witness {n : ℕ} {a : ℝ} (hn : 0 < n) (ha : 0 < a)
    (hK : 4 ≤ paperK n) (hu : 1 ≤ paperU n)
    (hKu : 32*paperU n ≤ (paperK n:ℝ))
    (hErr : 72*scoreB^3*(2*paperU n)^3/Real.sqrt (n:ℝ) ≤ 1)
    {x : Fin n → ℝ} (hx : x ∈ paperHitSet n a) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 2 ∧
      ENNReal.ofReal (Real.exp (paperU n^2/2-2)) <
        cubeAverage (tensorRho (paperK n) n) x r := by
  obtain ⟨j,hj⟩ := mem_iUnion.mp hx
  obtain ⟨hjM,hx⟩ := mem_iUnion.mp hj
  have w := paperGrid_window (paperK n) ha (zero_lt_one.trans_le hu) hjM
  exact ⟨rfun (paperK n) (paperGrid (paperK n) a (paperU n) j),
    hitPoint_cubeAverage_witness hK hn hu hKu w hErr hx⟩

end CenteredCube.RudinDensity

#print axioms CenteredCube.RudinDensity.eventually_scale_bounds
#print axioms CenteredCube.RudinDensity.lower_from_grid_mass
#print axioms CenteredCube.RudinDensity.paper_hit_cube_witness
