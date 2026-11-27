import AnchorCellGrid
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
namespace CubeBrownian

noncomputable def anchorDrift (c θ : ℝ) (anchor left : ℝ≥0) : ℝ :=
  if anchor ≤ left then 0 else θ*c^2

noncomputable def anchorTiltedMeasure {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (B : ℝ≥0 → Ω → ℝ) (c θ : ℝ) (anchor : ℝ≥0) : Measure Ω :=
  μ.tilted (fun w ↦ θ*c*(B anchor w-B 0 w))

noncomputable def anchorCellCentered {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (c θ : ℝ)
    (anchor left : ℝ≥0) (w : Ω) (s : ℝ≥0) : ℝ :=
  c*(B (left+s) w-B left w) - anchorDrift c θ anchor left * (s:ℝ)

theorem anchorCell_dyadic_centered_law {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)
    (hmB : ∀ t, Measurable (B t)) (c θ : ℝ)
    (anchor left A : ℝ≥0) (hA : anchor ≤ left ∨ left+A ≤ anchor) (r : ℕ) :
    let h := A/(2:ℝ≥0)^r
    let v := NNReal.mk (c^2) (sq_nonneg c)*h
    (anchorTiltedMeasure μ B c θ anchor).map
      (fun w ↦ dyadicIncrements A r (anchorCellCentered B c θ anchor left w)) =
      Measure.pi (fun _ : Fin (2^r) ↦ gaussianReal 0 v) := by
  dsimp only
  let N : ℕ := 2^r
  let h := A/(2:ℝ≥0)^r
  let v := NNReal.mk (c^2) (sq_nonneg c)*h
  let m := anchorDrift c θ anchor left
  let t : Fin (N+3+1) → ℝ≥0 := fun i ↦ anchorCellTimes anchor left A r i
  let j : Fin (N+3+1) := anchorCellIndex anchor left r
  let D := anchorGridIncrements B c t
  let Q := anchorTiltedMeasure μ B c θ anchor
  let e (i : Fin N) : Fin (N+3) := ⟨(i:ℕ)+2,by have hi := i.isLt; omega⟩
  have he : Function.Injective e := by
    intro i k hIK
    apply Fin.ext
    have hh := congrArg Fin.val hIK
    change (i:ℕ)+2 = (k:ℕ)+2 at hh
    omega
  have ht : Monotone t := fun _ _ hij ↦ anchorCellTimes_mono anchor left A r hij
  have h0 : t 0 = 0 := by simp [t,anchorCellTimes]
  have hj : t j = anchor := anchorCellTimes_anchor r hA
  let V (i : Fin (N+3)) := NNReal.mk (c^2) (sq_nonneg c) * nndist (t i.succ).1 (t i.castSucc).1
  let P (i : Fin (N+3)) := gaussianReal (if (i:ℕ)<(j:ℕ) then θ*(V i:ℝ) else 0) (V i)
  have hD : Q.map D = Measure.pi P := by
    have H := brownian_anchor_tilt_grid_law μ hB hmB c θ t ht j
    dsimp only at H
    rwa [hj,h0] at H
  have hmD : Measurable D := measurable_pi_iff.mpr (fun i ↦
    measurable_const.mul ((hmB (t i.succ)).sub (hmB (t i.castSucc))))
  have ht1 (i : Fin N) : t (e i).succ = left+dyadicT A r ((i:ℕ)+1) := by
    have hi := i.isLt
    change anchorCellTimes anchor left A r ((i:ℕ)+2+1) = _
    rw [show (i:ℕ)+2+1 = (i:ℕ)+1+2 by omega]
    exact anchorCellTimes_offset anchor left A r _ (by simpa only [N] using Nat.succ_le_of_lt hi)
  have ht0 (i : Fin N) : t (e i).castSucc = left+dyadicT A r i :=
    anchorCellTimes_offset anchor left A r _ i.isLt.le
  have hDist (i : Fin N) : (t (e i).succ : ℝ)-(t (e i).castSucc : ℝ) = (h:ℝ) := by
    rw [ht1,ht0]
    push_cast
    have hd := dyadicT_succ_sub A r (i:ℕ)
    change (dyadicT A r ((i:ℕ)+1):ℝ)-(dyadicT A r (i:ℕ):ℝ) = (h:ℝ) at hd
    linarith only [hd]
  have hV (i : Fin N) : V (e i) = v := by
    suffices hh : nndist (t (e i).succ).1 (t (e i).castSucc).1 = h by simp only [V,hh,v]
    apply NNReal.eq
    rw [show (↑(nndist (t (e i).succ).1 (t (e i).castSucc).1) : ℝ) =
      dist (t (e i).succ : ℝ) (t (e i).castSucc : ℝ) from rfl, Real.dist_eq,hDist]
    exact abs_of_nonneg (NNReal.coe_nonneg h)
  have hP (i : Fin N) : P (e i) = gaussianReal (m*(h:ℝ)) v := by
    dsimp only [P]
    rw [hV]
    by_cases hL : anchor ≤ left
    · have hJ : (j:ℕ) = 1 := by simp [j,anchorCellIndex,hL]
      rw [hJ,ite_eq_right (by change ¬ (i:ℕ)+2<1; omega)]
      simp [m,anchorDrift,hL]
    · have hJ : (j:ℕ) = N+3 := by simp [j,anchorCellIndex,hL,N]
      rw [hJ,ite_eq_left (by change (i:ℕ)+2<N+3; have hi := i.isLt; omega)]
      congr 1
      dsimp only [m,anchorDrift,v]
      rw [ite_eq_right hL]
      push_cast
      ring
  let p (x : Fin (N+3) → ℝ) (i : Fin N) := x (e i)
  have hmp : Measurable p := measurable_pi_iff.mpr (fun i ↦ measurable_pi_apply (e i))
  have : ∀ i, IsProbabilityMeasure (P i) := fun _ ↦ by dsimp [P]; infer_instance
  have hProj : (Q.map D).map p = Measure.pi (fun _ : Fin N ↦ gaussianReal (m*(h:ℝ)) v) := by
    rw [hD,pi_injective_projection P e he]
    exact congrArg Measure.pi (funext hP)
  let S (x : Fin N → ℝ) (i : Fin N) := x i + -(m*(h:ℝ))
  have hmS : Measurable S :=
    measurable_pi_iff.mpr (fun i ↦ (measurable_pi_apply i).add measurable_const)
  have heq : (fun w ↦ dyadicIncrements A r (anchorCellCentered B c θ anchor left w)) =
      S ∘ (p ∘ D) := by
    funext w i
    change (c*(B (left+dyadicT A r ((i:ℕ)+1)) w-B left w)-m*(dyadicT A r ((i:ℕ)+1):ℝ))-
      (c*(B (left+dyadicT A r (i:ℕ)) w-B left w)-m*(dyadicT A r (i:ℕ):ℝ)) =
      c*(B (t (e i).succ) w-B (t (e i).castSucc) w) + -(m*(h:ℝ))
    rw [ht1,ht0]
    have hd := dyadicT_succ_sub A r (i:ℕ)
    change (dyadicT A r ((i:ℕ)+1):ℝ)-(dyadicT A r (i:ℕ):ℝ) = (h:ℝ) at hd
    nlinarith only [congrArg (m * ·) hd]
  rw [heq,← Measure.map_map hmS (hmp.comp hmD),← Measure.map_map hmp hmD,hProj]
  let sh : ℝ → ℝ := fun x ↦ x + -(m*(h:ℝ))
  have hmSh : Measurable sh := by dsimp [sh]; fun_prop
  have hGauss : (gaussianReal (m*(h:ℝ)) v).map sh = gaussianReal 0 v := by
    simpa only [sh,add_neg_cancel] using gaussianReal_map_add_const (μ:=m*(h:ℝ)) (v:=v) (-(m*(h:ℝ)))
  have : ∀ _ : Fin N, SigmaFinite ((gaussianReal (m*(h:ℝ)) v).map sh) := fun _ ↦ by
    rw [hGauss]
    infer_instance
  change (Measure.pi (fun _ : Fin N ↦ gaussianReal (m*(h:ℝ)) v)).map
    (fun x i ↦ sh (x i)) = Measure.pi (fun _ : Fin N ↦ gaussianReal 0 v)
  rw [Measure.pi_map_pi (fun _ ↦ hmSh.aemeasurable)]
  simp only [hGauss]
end CubeBrownian
#print axioms CubeBrownian.anchorCell_dyadic_centered_law
