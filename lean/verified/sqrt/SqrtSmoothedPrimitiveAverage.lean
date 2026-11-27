import SqrtSmoothedPrimitiveCell
import SqrtRawTranslationL2

namespace CenteredCubeSqrt
open MeasureTheory Set
open scoped Interval
set_option maxHeartbeats 1000000

theorem box_prefix_eq_threshold_average {δ l h : ℝ} (hδ : 0<δ) (hlh : l≤h)
    (hl : l≤-δ/2) :
    (∫ z in l..h, boxWindowDensity δ z) =
      (1/δ)*(∫ z in -δ/2..δ/2, if z≤h then (1:ℝ) else 0) := by
  have hs : -δ/2≤δ/2 := by linarith
  rw [intervalIntegral.integral_of_le hlh,intervalIntegral.integral_of_le hs,
    setIntegral_congr_set Ioc_ae_eq_Icc,setIntegral_congr_set (μ:=volume) (s:=Ioc (-δ/2) (δ/2)) Ioc_ae_eq_Icc]
  have hI : (fun z : ℝ => if z≤h then (1:ℝ) else 0) = (Iic h).indicator (fun _ => 1) := by
    funext z
    by_cases hz : z≤h <;> simp [hz]
  unfold boxWindowDensity
  rw [hI,integral_indicator measurableSet_Icc,integral_indicator measurableSet_Iic,
    Measure.restrict_restrict measurableSet_Icc,Measure.restrict_restrict measurableSet_Iic]
  have he : Icc (-δ/2) (δ/2) ∩ Icc l h = Iic h ∩ Icc (-δ/2) (δ/2) := by
    ext z
    simp only [mem_inter_iff,mem_Icc,mem_Iic]
    exact ⟨fun a => ⟨a.2.2,a.1⟩,fun a => ⟨a.2,hl.trans a.2.1,a.1⟩⟩
  rw [he]
  simp [mul_comm]

theorem rawPrimitive_reflected_integrable {B K : ℕ} [NeZero K] (f : ZMod K→Fin B)
    (x l u : ℝ) : IntervalIntegrable (fun z => actualRawPrimitive f (x-z)) volume l u := by
  rw [intervalIntegrable_iff]
  apply Measure.integrableOn_of_bounded (M:=1) (s_finite:=by rw [uIoc]; simp [Real.volume_Ioc])
    ((actualRawPrimitive_measurable f).comp (measurable_const.sub measurable_id)).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro z
  change ‖actualRawPrimitive f (x-z)‖≤1
  simpa only [Real.norm_eq_abs] using actualRawPrimitive_abs_le_one f (x-z)

theorem actualAtomicPrimitive_is_box_average {B K : ℕ} [NeZero K]
    (hB : 0<B) (hK : 2≤K) (f : ZMod K→Fin B) {δ : ℝ}
    (hδ0 : 0<δ) (hδ : δ<1/((B:ℝ)*K)) (x : ℝ) :
    actualAtomicPrimitive f δ x =
      (1/δ)*(∫ z in -δ/2..δ/2, actualRawPrimitive f (x-z)) := by
  let k : ℤ := ⌊(K:ℝ)*x⌋
  let r := (K:ℝ)*x-(k:ℝ)
  let u := labelCellMidpoint (f (k:ZMod K))
  let c := ((k:ℝ)+u)/(K:ℝ)
  let g := (k:ℝ)/(K:ℝ)
  have hk : 0<(K:ℝ) := by exact_mod_cast (show 0<K by omega)
  have hb : 0<(B:ℝ) := by exact_mod_cast hB
  have hr : r∈Icc (0:ℝ) 1 :=
    ⟨Int.fract_nonneg ((K:ℝ)*x), (Int.fract_lt_one ((K:ℝ)*x)).le⟩
  have xx : x=((k:ℝ)+r)/(K:ℝ) := by dsimp [r]; field_simp; ring
  have hdel : (K:ℝ)*(δ/2)<1/(2*(B:ℝ)) := by
    apply (lt_div_iff₀ (by positivity)).mpr
    have hh := (lt_div_iff₀ (mul_pos hb hk)).mp hδ
    nlinarith
  have c0 : g-c≤-δ/2 := by
    have hu := (labelCellMidpoint_sharp (f (k:ZMod K))).1
    have e : g-c= -u/(K:ℝ) := by dsimp [g,c]; ring
    rw [e]
    apply (div_le_iff₀ hk).mpr
    linarith
  have c1 : g-c≤x-c := by
    have hh : g≤x := by rw [xx]; exact div_le_div_of_nonneg_right (by linarith [hr.1]) hk.le
    linarith
  have eq (z : ℝ) (hz : z∈Icc (-δ/2) (δ/2)) :
      actualRawPrimitive f (x-z) = (if z≤x-c then 1 else 0)-(r-(K:ℝ)*z) := by
    have e : x-z=((k:ℝ)+(r-(K:ℝ)*z))/(K:ℝ) := by rw [xx]; field_simp; ring
    have zl := mul_le_mul_of_nonneg_left hz.1 hk.le
    have zu := mul_le_mul_of_nonneg_left hz.2 hk.le
    rw [e,actualRawPrimitive_extended_cell f k (r-(K:ℝ)*z) hB
      (by linarith [hr.1]) (by linarith [hr.2])]
    have e' : u≤r-(K:ℝ)*z ↔ z≤x-c := by
      have er : (K:ℝ)*(x-c)=r-u := by dsimp [c,r]; field_simp; ring
      constructor
      · intro h
        apply (mul_le_mul_iff_of_pos_left hk).mp
        linarith
      · intro h
        have h' := mul_le_mul_of_nonneg_left h hk.le
        linarith
    unfold cellPrimitive
    change (if u≤r-(K:ℝ)*z then (1:ℝ) else 0)-(r-(K:ℝ)*z) = _
    by_cases hz' : z≤x-c
    · rw [ite_eq_left (e'.mpr hz'),ite_eq_left hz']
    · rw [ite_eq_right (fun hn => hz' (e'.mp hn)),ite_eq_right hz']
  have hs : -δ/2≤δ/2 := by linarith
  have hR := actualSmoothedPrimitive_cell_prefix hB hK f hδ0 hδ k hr
  rw [←xx] at hR
  change actualAtomicPrimitive f δ x=(∫ y in g..x,boxWindowDensity δ (y-c))-r at hR
  rw [hR,intervalIntegral.integral_comp_sub_right,box_prefix_eq_threshold_average hδ0 c1 c0,
    intervalIntegral.integral_congr (fun z hz => eq z (by rwa [uIcc_of_le hs] at hz))]
  have ha : IntervalIntegrable (fun z => if z≤x-c then (1:ℝ) else 0) volume (-δ/2) (δ/2) := by
    have hm : Measurable (fun z : ℝ => if z≤x-c then (1:ℝ) else 0) :=
      Measurable.ite (measurableSet_Iic : MeasurableSet (Iic (x-c))) measurable_const measurable_const
    rw [intervalIntegrable_iff]
    apply Measure.integrableOn_of_bounded (M:=1) (s_finite:=by rw [uIoc]; simp [Real.volume_Ioc])
      hm.aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun z => by split <;> norm_num)
  have hlin : IntervalIntegrable (fun z : ℝ => (K:ℝ)*z) volume (-δ/2) (δ/2) :=
    (continuous_id.const_mul _).intervalIntegrable _ _
  have hsub : IntervalIntegrable (fun z : ℝ => r-(K:ℝ)*z) volume (-δ/2) (δ/2) :=
    intervalIntegrable_const.sub hlin
  have tail : (∫ z in -δ/2..δ/2, r-(K:ℝ)*z)=δ*r := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const hlin,
      intervalIntegral.integral_const,intervalIntegral.integral_const_mul,integral_id]
    simp only [smul_eq_mul]
    ring
  rw [intervalIntegral.integral_sub ha hsub,tail]
  field_simp

theorem actualAtomicWindow_is_box_average {B K : ℕ} [NeZero K]
    (hB : 0<B) (hK : 2≤K) (f : ZMod K→Fin B) {δ : ℝ}
    (hδ0 : 0<δ) (hδ : δ<1/((B:ℝ)*K)) (L x : ℝ) :
    actualAtomicWindow f δ L x =
      (1/δ)*(∫ z in -δ/2..δ/2, actualRawWindow f L (x-z)) := by
  rw [actualAtomicWindow_eq_primitive f hδ0 x,
    actualAtomicPrimitive_is_box_average hB hK f hδ0 hδ,
    actualAtomicPrimitive_is_box_average hB hK f hδ0 hδ]
  have eq (z : ℝ) : actualRawWindow f L (x-z) =
      actualRawPrimitive f (x+L/2-z)-actualRawPrimitive f (x-L/2-z) := by
    unfold actualRawWindow
    rw [show x-z+L/2=x+L/2-z by ring,show x-z-L/2=x-L/2-z by ring]
  simp_rw [eq]
  rw [intervalIntegral.integral_sub (rawPrimitive_reflected_integrable f (x+L/2) _ _)
    (rawPrimitive_reflected_integrable f (x-L/2) _ _)]
  ring

#print axioms actualAtomicPrimitive_is_box_average
#print axioms actualAtomicWindow_is_box_average
end CenteredCubeSqrt
