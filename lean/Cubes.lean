import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

open Set MeasureTheory
open scoped ENNReal NNReal

namespace CenteredCube

abbrev Space (n : ℕ) := Fin n → ℝ

/-- Axis-parallel closed cube centered at x, with side length r. -/
noncomputable def cube {n : ℕ} (x : Space n) (r : ℝ) : Set (Space n) :=
  Icc (fun i => x i - r / 2) (fun i => x i + r / 2)

/-- Box used in the periodic truncation. -/
noncomputable def box (n : ℕ) (R : ℝ) : Set (Space n) :=
  Icc (fun _ => -R) (fun _ => R)

theorem measurableSet_cube {n : ℕ} (x : Space n) (r : ℝ) :
    MeasurableSet (cube x r) := isClosed_Icc.measurableSet

theorem volume_cube {n : ℕ} (x : Space n) (r : ℝ) :
    volume (cube x r) = ENNReal.ofReal r ^ n := by
  rw [cube, Real.volume_Icc_pi]
  have h (i : Fin n) : x i + r / 2 - (x i - r / 2) = r := by ring
  simp [h]

/-- Section 3 uses this inclusion for x in the inner box and side lengths below 2. -/
theorem cube_subset_box {n : ℕ} {x : Space n} {R r : ℝ}
    (hx : x ∈ box n (R - 1)) (hr : r ≤ 2) :
    cube x r ⊆ box n R := by
  rintro y ⟨hlo, hhi⟩
  refine ⟨fun i => ?_, fun i => ?_⟩
  · have hxi := hx.1 i
    have hyi := hlo i
    change -(R - 1) ≤ x i at hxi
    change x i - r / 2 ≤ y i at hyi
    change -R ≤ y i
    linarith
  · have hxi := hx.2 i
    have hyi := hhi i
    change x i ≤ R - 1 at hxi
    change y i ≤ x i + r / 2 at hyi
    change y i ≤ R
    linarith

noncomputable def absMass {n : ℕ} (f : Space n → ℝ) : ℝ≥0∞ :=
  ∫⁻ y, ENNReal.ofReal |f y| ∂volume

noncomputable def cubeAverage {n : ℕ} (f : Space n → ℝ) (x : Space n) (r : ℝ) :
    ℝ≥0∞ :=
  (∫⁻ y in cube x r, ENNReal.ofReal |f y| ∂volume) / ENNReal.ofReal r ^ n

noncomputable def maximal {n : ℕ} (f : Space n → ℝ) (x : Space n) : ℝ≥0∞ :=
  ⨆ r : Ioi (0 : ℝ), cubeAverage f x r

noncomputable def weakRatio {n : ℕ} (f : Space n → ℝ) (threshold : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal threshold * volume {x | ENNReal.ofReal threshold < maximal f x} / absMass f

noncomputable def weakConstant (n : ℕ) : ℝ≥0∞ :=
  ⨆ f : {f : Space n → ℝ // Integrable f volume ∧ 0 < absMass f},
    ⨆ threshold : Ioi (0 : ℝ), weakRatio f.val threshold

theorem average_le_maximal {n : ℕ} (f : Space n → ℝ) (x : Space n) {r : ℝ}
    (hr : 0 < r) : cubeAverage f x r ≤ maximal f x :=
  le_iSup (fun r : Ioi (0 : ℝ) => cubeAverage f x r) ⟨r, hr⟩

theorem weakRatio_le_constant {n : ℕ} (f : Space n → ℝ)
    (hf : Integrable f volume) (hm : 0 < absMass f) {threshold : ℝ} (hthreshold : 0 < threshold) :
    weakRatio f threshold ≤ weakConstant n := by
  unfold weakConstant
  exact le_trans (le_iSup (fun t : Ioi (0 : ℝ) => weakRatio f t) ⟨threshold, hthreshold⟩)
    (le_iSup (fun g : {g : Space n → ℝ // Integrable g volume ∧ 0 < absMass g} =>
      ⨆ t : Ioi (0 : ℝ), weakRatio g.val t) ⟨f, hf, hm⟩)

/-- Truncating to the outer box preserves every average used at inner points. -/
theorem truncated_average {n : ℕ} (f : Space n → ℝ) {x : Space n} {R r : ℝ}
    (hx : x ∈ box n (R - 1)) (hr : r ≤ 2) :
    cubeAverage ((box n R).indicator f) x r = cubeAverage f x r := by
  unfold cubeAverage
  congr 1
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem (measurableSet_cube x r)] with y hy
  rw [Set.indicator_of_mem (cube_subset_box hx hr hy)]

theorem halo_of_truncated_average {n : ℕ} (f : Space n → ℝ)
    {x : Space n} {R r threshold : ℝ} (hx : x ∈ box n (R - 1))
    (hr₀ : 0 < r) (hr : r ≤ 2) (havg : ENNReal.ofReal threshold < cubeAverage f x r) :
    ENNReal.ofReal threshold < maximal ((box n R).indicator f) x := by
  rw [← truncated_average f hx hr] at havg
  exact havg.trans_le (average_le_maximal _ _ hr₀)

/-- A set with a pointwise witnessing cube contributes its full measure to the weak ratio. -/
theorem lower_bound_of_average_on_set {n : ℕ} {f : Space n → ℝ} {E : Set (Space n)}
    {threshold : ℝ} (hf : Integrable f volume) (hm : 0 < absMass f) (hthreshold : 0 < threshold)
    (hE : ∀ x ∈ E, ∃ r > 0, ENNReal.ofReal threshold < cubeAverage f x r) :
    ENNReal.ofReal threshold * volume E / absMass f ≤ weakConstant n := by
  have hsub : E ⊆ {x | ENNReal.ofReal threshold < maximal f x} := by
    intro x hx
    obtain ⟨r, hr, havg⟩ := hE x hx
    exact havg.trans_le (average_le_maximal f x hr)
  apply le_trans _ (weakRatio_le_constant f hf hm hthreshold)
  unfold weakRatio
  have hvol : volume E ≤ volume {x | ENNReal.ofReal threshold < maximal f x} :=
    measure_mono hsub
  gcongr

/-- Bernoulli's inequality gives the paper's factor 1/2 for R=n². -/
theorem truncation_retention {n : ℕ} (hn : 2 ≤ n) :
    (1 / 2 : ℝ) ≤ (1 - 1 / (n : ℝ)^2)^n := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : (0 : ℝ) < n := by linarith
  have hpos : (0 : ℝ) < (n : ℝ)^2 := by positivity
  have hsq : (1 : ℝ) ≤ (n : ℝ)^2 := by nlinarith
  have hsmall : (1 : ℝ) / (n : ℝ)^2 ≤ 1 := (div_le_one hpos).mpr hsq
  have hbern := one_add_mul_le_pow (a := -(1 / (n : ℝ)^2))
    (show (-2 : ℝ) ≤ -(1 / (n : ℝ)^2) by linarith) n
  have hcancel : (n : ℝ) * (1 / (n : ℝ)^2) = 1 / n := by
    field_simp
  rw [mul_neg, hcancel, ← sub_eq_add_neg, ← sub_eq_add_neg] at hbern
  have hhalf : (1 : ℝ) / (n : ℝ) ≤ 1 / 2 := (div_le_iff₀ hp).mpr (by linarith)
  exact (show (1 / 2 : ℝ) ≤ 1 - 1 / n by linarith).trans hbern

/-- The asymptotic weak-constant inequality in the Rudin–Shapiro paper. -/
def SqrtLogLowerBound : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
    ENNReal.ofReal (c * Real.sqrt (n : ℝ) / Real.log (n : ℝ)) ≤ weakConstant n

private theorem exp_half_log {x : ℝ} (hx : 0 < x) :
    Real.exp (Real.log x / 2) = Real.sqrt x := by
  apply (sq_eq_sq₀ (Real.exp_pos _).le (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt hx.le, pow_two, ← Real.exp_add,
    show Real.log x / 2 + Real.log x / 2 = Real.log x by ring, Real.exp_log hx]

/-- The last step of the paper, after supplying the measured halo and the
mass of the truncated test function. The assumptions display the remaining
analytic inputs explicitly. -/
theorem sqrtLog_of_truncated_halo {n : ℕ} (hn : 2 ≤ n) {c h : ℝ} (hc : 0 < c)
    (hheight : Real.log (n : ℝ) / 2 - 5 / 2 ≤ h)
    (g : Space n → ℝ) (E : Set (Space n))
    (hf : Integrable ((box n ((n : ℝ)^2)).indicator g) volume)
    (hmass : absMass ((box n ((n : ℝ)^2)).indicator g) =
      ENNReal.ofReal ((2 * (n : ℝ)^2)^n))
    (hvolume : ENNReal.ofReal ((c / Real.log (n : ℝ)) * (2 * (n : ℝ)^2 - 2)^n)
      ≤ volume E)
    (hE : ∀ x ∈ E, x ∈ box n ((n : ℝ)^2 - 1) ∧
      ∃ r : ℝ, 0 < r ∧ r ≤ 2 ∧ ENNReal.ofReal (Real.exp h) < cubeAverage g x r) :
    ENNReal.ofReal ((c * Real.exp (-(5 / 2)) / 2) *
      Real.sqrt (n : ℝ) / Real.log (n : ℝ)) ≤ weakConstant n := by
  let L := Real.log (n : ℝ)
  let R := (n : ℝ)^2
  let f := (box n R).indicator g
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hR : 0 < R := by dsimp [R]; positivity
  have hL : 0 < L := Real.log_pos (by linarith)
  have hinner : 0 ≤ 2 * R - 2 := by dsimp [R]; nlinarith
  have hmassPos : 0 < (2 * R)^n := pow_pos (by positivity) _
  have hvolPos : 0 ≤ (c / L) * (2 * R - 2)^n := by positivity
  have havg : ∀ x ∈ E, ∃ r > 0, ENNReal.ofReal (Real.exp h) < cubeAverage f x r := by
    intro x hx
    obtain ⟨hinnerBox, r, hrad, hrad2, havg⟩ := hE x hx
    exact ⟨r, hrad, (truncated_average g hinnerBox hrad2).symm ▸ havg⟩
  have hC := lower_bound_of_average_on_set hf
    (by rw [hmass]; exact ENNReal.ofReal_pos.mpr hmassPos)
    (Real.exp_pos _) havg
  rw [hmass] at hC
  have hv : ENNReal.ofReal (Real.exp h * ((c / L) * (2 * R - 2)^n) / (2 * R)^n)
      ≤ weakConstant n := by
    rw [ENNReal.ofReal_div_of_pos hmassPos, ENNReal.ofReal_mul (Real.exp_pos _).le]
    exact (show ENNReal.ofReal (Real.exp h) * ENNReal.ofReal ((c / L) * (2 * R - 2)^n) /
        ENNReal.ofReal ((2 * R)^n) ≤ _ by gcongr).trans hC
  have hpow : ((2 * R - 2) / (2 * R))^n = (1 - 1 / (n : ℝ)^2)^n := by
    congr 1
    dsimp [R]
    field_simp
  have hr : (1 / 2 : ℝ) ≤ (1 - 1 / (n : ℝ)^2)^n := truncation_retention hn
  have hexp : Real.exp (-(5 / 2)) * Real.sqrt (n : ℝ) ≤ Real.exp h := by
    rw [← exp_half_log hnpos, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith
  refine (ENNReal.ofReal_le_ofReal ?_).trans hv
  calc
    c * Real.exp (-(5 / 2)) / 2 * Real.sqrt (n : ℝ) / Real.log n =
        (c / L) * (Real.exp (-(5 / 2)) * Real.sqrt (n : ℝ)) * (1 / 2) := by
      dsimp [L]
      ring
    _ ≤ (c / L) * Real.exp h * (1 - 1 / (n : ℝ)^2)^n := by
      gcongr
    _ = Real.exp h * ((c / L) * (2 * R - 2)^n) / (2 * R)^n := by
      rw [← hpow, div_pow]
      ring

end CenteredCube

#print axioms CenteredCube.volume_cube
#print axioms CenteredCube.truncated_average
#print axioms CenteredCube.halo_of_truncated_average
#print axioms CenteredCube.lower_bound_of_average_on_set
#print axioms CenteredCube.truncation_retention

#print axioms CenteredCube.sqrtLog_of_truncated_halo
