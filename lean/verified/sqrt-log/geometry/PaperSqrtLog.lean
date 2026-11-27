import PhysicalGrid
import PeriodicEndgame
import PairGrowth

open Filter MeasureTheory Set
open scoped Topology ENNReal

namespace CenteredCube.RudinDensity

set_option maxHeartbeats 600000

theorem paper_grid_probability {n : ℕ} {a : ℝ} (hn : 0 < n) (ha : 0 < a)
    (hSpacing : singleUpper/(Real.exp (a^2)-1) ≤ marginalC/4)
    (hK : 64 ≤ paperK n) (hu : 1 ≤ paperU n) (hKu : 32*paperU n ≤ (paperK n:ℝ))
    (hKB : 2*paperU n^2/a^2 ≤ (paperK n:ℝ))
    (hKE : (2*Real.pi*64+8)/(paperK n:ℝ) ≤ min globalMu globalNu/2)
    (hN : readyMD n scoreB) (hWin : (2*paperU n)^6 ≤ (n:ℝ))
    (hErr : 72*scoreB^3*(2*paperU n)^3/Real.sqrt (n:ℝ) ≤ 1)
    (hLoss : paperU n^2+Real.log (2/singleLower) ≤
      (n:ℝ)/(32*(scoreB^2+1)^2*paperU n^4))
    (hN₂ : readyMD n (pairB (globalNu/2)))
    (hWin₂ : (2*paperU n/Real.sqrt (2*(globalNu/2)))^6 ≤ (n:ℝ))
    (hErr₂ : 72*(pairB (globalNu/2))^3*(2*paperU n/Real.sqrt (2*(globalNu/2)))^3/
      Real.sqrt (n:ℝ) ≤ 1)
    (hMid : singleUpper*((32*paperU n/a+1)*Real.exp (-lagDelta*paperU n^2)) ≤ marginalC/12)
    (hOuter : singleUpper*((paperU n^3*paperU n/a+1)*Real.exp (-(1/6)*paperU n^2)) ≤ marginalC/12)
    (hFar : singleUpper*((paperGridM (paperK n) a:ℝ)*Real.exp (-(paperU n^2/2)) *
        Real.exp (lagTheta (paperK n) (paperU n)*paperU n^2/
          (1+lagTheta (paperK n) (paperU n)))) ≤ marginalC/6) :
    (paperGridM (paperK n) a:ℝ)*rawMarginal (paperU n)/2 ≤
      (cellLaw n).real (paperHitSet n a) := by
  let u := paperU n
  let K := paperK n
  let M := paperGridM K a
  let t := paperGrid K a u
  have hK' : 4 ≤ K := by omega
  have hu0 : 0 < u := zero_lt_one.trans_le hu
  have hM0 : 0 ≤ (M:ℝ) := by positivity
  have hθ : 0 ≤ lagTheta K u := by unfold lagTheta; positivity
  have hwind : ∀ i < M, |t i-(K:ℝ)/4| ≤ (K:ℝ)/(100*u) :=
    fun _ hi => paperGrid_window K ha hu0 hi
  have hNear := budget_convert_near hM0 hu0 hSpacing
  have hMid' := budget_convert_mid hM0 hu0 hMid
  have hOuter' := budget_convert_outer hM0 hu0 hOuter
  have hFar' := budget_convert_far hM0 hu0 hθ
    (by simpa only [mul_assoc] using hFar)
  have hcenter : centerScale n K = u := (paperU_is_centerScale n).symm
  have hM : ∀ i < M, rawMarginal u ≤ (cellLaw n).real (hitPoint n K (t i)) := by
    intro i hi
    simpa only [rawMarginal, marginalC, div_div,hcenter] using
      (one_point_good_actual_bound hK' hn hu hKu (hwind i hi) hN hWin hErr hLoss).1
  unfold paperHitSet
  exact grid_union_lower hn hK hu ha hKB hKE t hwind
    (fun _ _ hij _ => paperGrid_lag K ha hu0 hij) (fun i => hitPoint n K (t i))
    (fun i => measurableSet_hitPoint n K (t i))
    (fun i hi => hitPoint_subset_raw hK' hu hKu (hwind i hi))
    hM hN₂ hWin₂ hErr₂ hNear hMid' hOuter' hFar'

theorem eventually_paper_grid_witness {a : ℝ} (ha : 0 < a)
    (hSpacing : singleUpper/(Real.exp (a^2)-1) ≤ marginalC/4) :
    ∀ᶠ n : ℕ in atTop,
      paperHaloC a / Real.log (n:ℝ) ≤ (cellLaw n).real (paperHitSet n a) ∧
      (∀ x ∈ paperHitSet n a, ∃ r : ℝ, 0 < r ∧ r ≤ 2 ∧
        ENNReal.ofReal (Real.exp (paperU n^2/2-2)) <
          cubeAverage (tensorRho (paperK n) n) x r) := by
  filter_upwards [eventually_rounded_height, eventually_paperK_pos, eventually_grid_large ha,
    log_nat_tends_top.eventually_ge_atTop 1, eventually_scale_bounds ha,
    eventually_onepoint_conditions, eventually_twopoint_conditions_globalNu,
    eventually_overlap_ratios ha] with n hround hk hlarge hlog hscale hOne hTwo hRatios
  obtain ⟨hn,hK,hu,hKu,hN,hWin,hErr,hLoss⟩ := hOne (paperK n) hk hround
  obtain ⟨hN₂,hWin₂,hErr₂⟩ := hTwo (paperU n) hu hround
  obtain ⟨hK64,hKB,hKE⟩ := hscale
  obtain ⟨hMid,hOuter,hFar⟩ := hRatios
  have h := paper_grid_probability hn ha hSpacing hK64 hu hKu hKB hKE
    hN hWin hErr hLoss hN₂ hWin₂ hErr₂ hMid hOuter hFar
  exact ⟨(lower_from_grid_mass hn ha hk hlog hlarge hround).trans h,
    fun _ hx => paper_hit_cube_witness hn ha hK hu hKu hErr hx⟩

/-- The full unconditioned centred-cube lower bound at order sqrt(n)/log(n). -/
theorem sqrtLogLowerBound_paper : SqrtLogLowerBound := by
  obtain ⟨a,ha,hSpacing⟩ := exists_fixed_spacing
  have HC : 0 < paperHaloC a := paperHaloC_pos ha
  obtain ⟨N,hN⟩ := eventually_atTop.1 ((eventually_paper_grid_witness ha hSpacing).and
    (eventually_rounded_height.and ((eventually_ge_atTop (2:ℕ)).and eventually_paperK_pos)))
  apply sqrtLogLowerBound_of_haloData HC (N₀ := N)
  intro n hn
  obtain ⟨⟨hMass,hW⟩,hErr,hn₂,hK⟩ := hN n hn
  have hheight : Real.log (n:ℝ)-1 ≤ paperU n^2 := by linarith only [(abs_le.mp hErr).1]
  exact haloDataOfProductCell hn₂ hK hheight (paperHitSet n a) (measurable_paperHitSet n a) hMass hW

end CenteredCube.RudinDensity

#print axioms CenteredCube.RudinDensity.paper_grid_probability
#print axioms CenteredCube.RudinDensity.eventually_paper_grid_witness
#print axioms CenteredCube.RudinDensity.sqrtLogLowerBound_paper
