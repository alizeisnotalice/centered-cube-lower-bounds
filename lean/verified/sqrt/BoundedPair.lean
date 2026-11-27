import PaperPair
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory Filter Set CubeBrownian
open scoped NNReal ENNReal Topology ProbabilityTheory
namespace CubeSqrtPair

theorem bounded_centered_fourth
    {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (V : Ω → ℝ) (hm : Measurable V) (b : ℝ) (hb : 0 ≤ b) (hB : ∀ w, |V w| ≤ b) :
    let m := ∫ w, V w ∂Q
    MemLp V 2 Q ∧ Integrable (fun w ↦ (V w-m)^4) Q ∧
      (∫ w, (V w-m)^4 ∂Q) ≤ (2*b)^2*Var[V;Q] := by
  dsimp only
  let m := ∫ w, V w ∂Q
  have h2 : MemLp V 2 Q := MemLp.of_bound hm.aestronglyMeasurable b
    (Eventually.of_forall fun w ↦ by simpa only [Real.norm_eq_abs] using hB w)
  have hM : |m| ≤ b := by
    change ‖∫ w, V w ∂Q‖ ≤ b
    calc
      _ ≤ ∫ w, ‖V w‖ ∂Q := norm_integral_le_integral_norm _
      _ ≤ ∫ _ : Ω, b ∂Q := integral_mono_ae (h2.integrable one_le_two).norm
        (integrable_const _) (Eventually.of_forall fun w ↦ by simpa only [Real.norm_eq_abs] using hB w)
      _ = _ := by simp
  have hC (w : Ω) : |V w-m| ≤ 2*b := (abs_sub _ _).trans (by linarith only [hB w,hM])
  have h4M : MemLp (fun w ↦ V w-m) 4 Q := MemLp.of_bound (hm.sub_const m).aestronglyMeasurable (2*b)
    (Eventually.of_forall fun w ↦ by simpa only [Real.norm_eq_abs] using hC w)
  have h4 : Integrable (fun w ↦ (V w-m)^4) Q := by
    have H : Integrable (fun w ↦ ‖V w-m‖^(4:ℕ)) Q := h4M.integrable_norm_pow'
    have hEq : (fun w ↦ ‖V w-m‖^(4:ℕ)) = fun w ↦ (V w-m)^4 := by
      funext w
      rw [Real.norm_eq_abs,show (4:ℕ)=2*2 by norm_num,pow_mul,sq_abs,← pow_mul]
    rwa [hEq] at H
  have hSquare := (memLp_two_iff_integrable_sq ((hm.sub_const m).aestronglyMeasurable)).1
    (show MemLp (fun w ↦ V w-m) 2 Q from h2.sub (memLp_const m))
  refine ⟨h2,h4,?_⟩
  rw [variance_eq_integral hm.aemeasurable,← integral_const_mul]
  apply integral_mono_ae h4 (hSquare.const_mul _)
  exact Eventually.of_forall fun w ↦ by
    have hsq : (V w-m)^2 ≤ (2*b)^2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hC w) 2
    change (V w-m)^4 ≤ (2*b)^2*(V w-m)^2
    rw [show (V w-m)^4 = (V w-m)^2*(V w-m)^2 by ring]
    exact mul_le_mul_of_nonneg_right hsq (sq_nonneg _)

/-- Uniform score cap gives the actual vanishing BE prefactor, with the exact
original Hellinger weight preserved. -/
theorem paper_pair_bounded
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (L J : Ω → ℝ)
    (hmL : Measurable L) (hmJ : Measurable J)
    (hInt : Integrable (fun w ↦ Real.exp (pairScore L J w)) P)
    (b : ℝ) (hb : 0 ≤ b) (hB : ∀ w, |pairScore L J w| ≤ b)
    {n : ℕ} (hn : 0 < n) (h : ℝ) (v : ℝ) (hv : 0 < v)
    (hVar : Var[pairScore L J;P.tilted (pairScore L J)] = v) :
    let s := Real.sqrt (n:ℝ)*Real.sqrt v
    let H := avgAffinity P L J
    let A : Set (Fin n → Ω) := {x | h < ∑ i, L (x i)}
    let B : Set (Fin n → Ω) := {x | h < ∑ i, J (x i)}
    Real.exp h * (Measure.pi (fun _ : Fin n ↦ P)).real (A∩B) ≤ H^n*((φ 0+120*b)/s) := by
  dsimp only
  let V := pairScore L J
  let Q := P.tilted V
  let m := ∫ w, V w ∂Q
  let m4 := ∫ w, (V w-m)^4 ∂Q
  let H := avgAffinity P L J
  let r := Real.sqrt (n:ℝ)
  let t := Real.sqrt v
  let s := r*t
  let _ : IsProbabilityMeasure Q := isProbabilityMeasure_tilted hInt
  have hT := bounded_centered_fourth Q V ((hmL.add hmJ).div_const 2) b hb hB
  have hPair := (paper_pair_actual P L J hmL hmJ hInt hT.1 hn h v hv hVar hT.2.1).2
  have hSQ : Real.sqrt m4 ≤ (2*b)*t := by
    have H := Real.sqrt_le_sqrt hT.2.2
    have hvv : Var[V;Q] = v := hVar
    rw [hvv,Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (by positivity)] at H
    exact H
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  have hr : 0 < r := Real.sqrt_pos.2 hnR
  have ht : 0 < t := Real.sqrt_pos.2 hv
  have ht2 : t^2 = v := Real.sq_sqrt hv.le
  have hs : 0 < s := mul_pos hr ht
  have hε : 30*Real.sqrt m4/(v*r) ≤ 60*b/s := by
    calc
      _ ≤ 30*((2*b)*t)/(v*r) := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hSQ (by norm_num)) (by positivity)
      _ = _ := by dsimp [s]; rw [← ht2]; field_simp [hr.ne',ht.ne'] <;> ring
  have hH : 0 ≤ H := integral_nonneg (fun _ ↦ (Real.exp_pos _).le)
  apply hPair.trans
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg hH _)
  change φ 0/s + 2*(30*Real.sqrt m4/(v*r)) ≤ _
  calc
    _ ≤ φ 0/s + 2*(60*b/s) := add_le_add_right (mul_le_mul_of_nonneg_left hε (by norm_num)) _
    _ = _ := by change _ = (φ 0+120*b)/s; ring

end CubeSqrtPair
#print axioms CubeSqrtPair.paper_pair_bounded
