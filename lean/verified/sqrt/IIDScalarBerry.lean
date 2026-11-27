import BerryClosedCDF
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory
namespace CubeSqrtPair
set_option maxHeartbeats 1000000

theorem iid_scalar_berry_cdf {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q] (V : Ω → ℝ)
    (hm : Measurable V) (h2 : MemLp V 2 Q)
    (m : ℝ) (hMean : ∫ x, V x ∂Q = m)
    (v : ℝ) (hv : 0 < v) (hVar : Var[V;Q] = v)
    (h3 : Integrable (fun x ↦ |V x-m|^3) Q)
    {n : ℕ} (hn : 0 < n) (a : ℝ) :
    let S (x : Fin n → Ω) := ∑ i, V (x i)
    let s := Real.sqrt (n : ℝ)*Real.sqrt v
    |((Measure.pi (fun _ : Fin n ↦ Q)).map (fun x ↦ (S x-(n:ℝ)*m)/s)).real (Iic a) -
      (gaussianReal 0 1).real (Iic a)| ≤
      30*((n:ℝ)*((∫ x, |V x-m|^3 ∂Q)/s^3)) := by
  dsimp only
  let s := Real.sqrt (n : ℝ)*Real.sqrt v
  let Y : Ω → ℝ := fun x ↦ (V x-m)/s
  let Qπ := Measure.pi (fun _ : Fin n ↦ Q)
  let Z : Fin n → (Fin n → Ω) → ℝ := fun i x ↦ Y (x i)
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  have hs : 0 < s := mul_pos (Real.sqrt_pos.2 hnR) (Real.sqrt_pos.2 hv)
  have hmY : Measurable Y := (hm.sub_const m).div_const s
  have hEv (i : Fin n) : MeasurePreserving (fun x : Fin n → Ω ↦ x i) Qπ Q :=
    measurePreserving_eval (fun _ : Fin n ↦ Q) i
  have hmZ (i : Fin n) : Measurable (Z i) := hmY.comp (hEv i).measurable
  have hiZ : iIndepFun Z Qπ := iIndepFun_pi (fun _i : Fin n ↦ hmY.aemeasurable)
  have hY2 : MemLp Y 2 Q := by
    simp only [Y,div_eq_inv_mul]
    exact (h2.sub (memLp_const m)).const_smul s⁻¹
  have hz2 (i : Fin n) : MemLp (Z i) 2 Qπ := hY2.comp_measurePreserving (hEv i)
  have hzmean (i : Fin n) : ∫ x, Z i x ∂Qπ = 0 := by
    rw [show (∫ x, Z i x ∂Qπ) = ∫ x, Y x ∂Q from
      integral_comp_eval (μ := fun _ : Fin n ↦ Q) (i:=i) (f:=Y) hmY.aestronglyMeasurable]
    simp only [Y]
    rw [integral_div,integral_sub (h2.integrable (by norm_num)) (integrable_const _),hMean]
    simp
  have hs2 : s^2 = (n:ℝ)*v := by
    rw [show s = Real.sqrt (n:ℝ)*Real.sqrt v from rfl,mul_pow,Real.sq_sqrt hnR.le,Real.sq_sqrt hv.le]
  have hYvar : Var[Y;Q] = (n:ℝ)⁻¹ := by
    simp only [Y,div_eq_inv_mul]
    rw [variance_const_mul,variance_sub_const hm.aestronglyMeasurable,hVar,inv_pow,hs2]
    field_simp [hnR.ne',hv.ne']
  have hAllVar : ∑ i, Var[Z i;Qπ] = 1 := by
    have hj (i : Fin n) : Var[Z i;Qπ] = (n:ℝ)⁻¹ := by
      rw [show Var[Z i;Qπ] = Var[Y;Q] from (hEv i).variance_fun_comp hmY.aemeasurable,hYvar]
    simp [hj,hnR.ne']
  have hY3 : Integrable (fun x ↦ |Y x|^3) Q := by
    simp only [Y,abs_div,abs_of_pos hs,div_pow]
    exact h3.div_const _
  have hz3 (i : Fin n) : Integrable (fun x ↦ |Z i x|^3) Qπ :=
    (hEv i).integrable_comp_of_integrable hY3
  have hz3' (i : Fin n) : (∫ x, |Z i x|^3 ∂Qπ) ≤ (∫ x, |V x-m|^3 ∂Q)/s^3 := by
    have hMeas : Measurable (fun x ↦ |Y x|^3) := (continuous_abs.measurable.comp hmY).pow_const _
    have hEq := integral_comp_eval (μ:=fun _ : Fin n ↦ Q) (i:=i)
      (f:=fun x ↦ |Y x|^3) hMeas.aestronglyMeasurable
    change (∫ x, |Z i x|^3 ∂Qπ) = ∫ x, |Y x|^3 ∂Q at hEq
    rw [hEq]
    simp only [Y,abs_div,abs_of_pos hs,div_pow,integral_div,le_refl]
  have hBE := CubeMD.fin_row_berry_closed_cdf hmZ hz2 hiZ hzmean hAllVar hz3 _ hz3' a
  have hEq : (fun x : Fin n → Ω ↦ ((∑ i, V (x i))-(n:ℝ)*m)/s) =
    fun x ↦ ∑ i, Z i x := by
    funext x
    change ((∑ i, V (x i))-(n:ℝ)*m)/s = ∑ i : Fin n, (V (x i)-m)/s
    rw [← Finset.sum_div,Finset.sum_sub_distrib]
    simp
  change |(Qπ.map (fun x ↦ ((∑ i, V (x i))-(n:ℝ)*m)/s)).real (Iic a) -
    (gaussianReal 0 1).real (Iic a)| ≤ _
  rw [hEq]
  exact hBE

end CubeSqrtPair
#print axioms CubeSqrtPair.iid_scalar_berry_cdf
