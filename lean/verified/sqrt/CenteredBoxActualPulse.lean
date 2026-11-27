import BoxNodeApproximation
import SqrtWindowPulse
import Mathlib.Tactic

namespace CubeBrownian
open Set MeasureTheory CenteredCubeSqrt
open scoped RealInnerProductSpace
set_option maxHeartbeats 900000

theorem centeredBoxNode_sub_is_actualPulse {e s t : ℝ} (he : 0<e) (hs : 0≤s) (hst : s≤t) (x : ℝ) :
    centeredBoxNode e t x-centeredBoxNode e s x=smoothedWindowPulse e s t x := by
  have hD : centeredBoxNode e t x-centeredBoxNode e s x=centeredBoxNode e (t-s) (x-s) := by
    unfold centeredBoxNode boxNode
    rw [show x+e/2-s=x-s+e/2 by ring,show x-s+e/2-(t-s)=x+e/2-t by ring]
    ring
  rw [hD,centeredBoxNode_eq_overlap he (sub_nonneg.mpr hst),smoothedWindowPulse_eq_overlap]
  have E : Icc (-e/2) (e/2) ∩ Icc (x-s-(t-s)) (x-s) =
      Icc (max (-e/2) (x-t)) (min (e/2) (x-s)) := by
    rw [show x-s-(t-s)=x-t by ring]
    ext z
    simp only [mem_inter_iff,mem_Icc,max_le_iff,le_min_iff]; tauto
  rw [E,Real.volume_Icc,ENNReal.toReal_ofReal']
  congr 2
  rw [min_def,max_def,min_def,max_def]
  split_ifs <;> linarith

theorem centeredBoxNodeL2_sq_eq_actualPulse {e s t : ℝ} (he : 0<e) (hs : 0≤s) (hst : s≤t) :
    ‖centeredBoxNodeL2 e t he (hs.trans hst)-centeredBoxNodeL2 e s he hs‖^2=
      pulseOverlap e s t s t 0 := by
  let f := centeredBoxNodeL2 e t he (hs.trans hst)
  let g := centeredBoxNodeL2 e s he hs
  have hf : (f : ℝ→ℝ) =ᵐ[volume] centeredBoxNode e t := MemLp.coeFn_toLp _
  have hg : (g : ℝ→ℝ) =ᵐ[volume] centeredBoxNode e s := MemLp.coeFn_toLp _
  change ‖f-g‖^2=_
  rw [←real_inner_self_eq_norm_sq,MeasureTheory.L2.inner_def]
  unfold pulseOverlap
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub f g,hf,hg] with x H Hf Hg
  rw [H,Pi.sub_apply,Hf,Hg,centeredBoxNode_sub_is_actualPulse he hs hst,
    real_inner_self_eq_norm_sq,Real.norm_eq_abs,sq_abs,sub_zero,pow_two]

#print axioms centeredBoxNodeL2_sq_eq_actualPulse
end CubeBrownian
